import std/[
  json,
  options,
  os,
  osproc,
  strformat,
  streams,
  strutils,
  sugar,
  wordwrap
]

const
  PrettyIndent = 2
    ## The amount of indentation to makes things pretty

type
  Pull = object
    ## Information about a pull request
    targetRepo: string
    number: Natural
    title, body: string
    baseCommit: string ## The commit to squash on top of

func wrapForCommit(s: string): string =
  ## Wrap the string `s` for use in a commit message
  wrapWords(s, 72)

func toCommitMsg(p: Pull): string =
  ## Create a commit message from `p`.
  let msgBody = p.body.split("\n---")[0].strip()

  result = &"""
{p.title} (#{p.number})

{wrapForCommit(msgBody)}"""

func `$`(p: Pull): string =
  ## Turn `p` into a human-readable string
  &"""
{p.title} ({p.targetRepo}#{p.number})


{p.body.wrapForCommit().indent(PrettyIndent)}


Base commit: {p.baseCommit}
"""

type
  GithubBackend = concept g
    ## Backend for interacting with Github
    g.available is bool
    ## Whether the backend can be used

    g.getPull is Option[Pull]
    ## Return the Pull request corresponding to the repository at the current
    ## directory

proc exec(cmd: string, args: varargs[string]) =
  ## Print and run `cmd` with `args` and raise an error on failure
  # The run command to print to users
  let runcmd = quoteShellCommand(cmd & @args)
  echo "Running: ", runcmd

  let p = startProcess(
    cmd, args = args, options = {poParentStreams, poStdErrToStdOut, poUsePath}
  )

  defer: close p

  let exitcode = p.waitForExit()
  if exitcode != 0:
    raise newException(CatchableError):
      &"The command {runcmd} exited with exit code: {exitcode}"

type
  CompletedRun = object
    exitcode: int
    output: string
    error: string

proc capture(cmd: string,
             args: varargs[string],
             input: Option[string]): CompletedRun =
  ## Run `cmd` with `args` and capture all of its outputs
  let p = startProcess(cmd, args = args, options = {poUsePath})
  defer: close p
  if input.isSome:
    p.inputStream.write(get input)
  # This is dangerous with osproc since it wasn't designed to handle this.
  # Since we are not doing any form of concurrency, however, the chance of
  # a fd popping up to be closed by mistake is near zero.
  close p.inputStream
  result.output = p.outputStream.readAll()
  result.error = p.errorStream.readAll()
  result.exitcode = p.waitForExit()

proc capture(cmd: string,
             args: varargs[string]): CompletedRun =
  capture(cmd, args, none(string))

type
  GithubCli = object
    ## Interact with Github via Github CLI

proc available(gh: GithubCli): bool =
  ## Whether Github CLI is available
  findExe("gh").len > 0

proc graphql(gh: GithubCli, inputs: JsonNode, query: string): JsonNode =
  ## Perform a GraphQL query, raise on query failure
  let graphqlQuery = %*{
    "query": query,
    "variables": inputs
  }

  let queryCall = capture(
    "gh", "api", "graphql", "--input", "-",
    input = some $graphqlQuery
  )
  # gh-api returns JSON for any errors, so no need to check for exit code
  result = parseJson queryCall.output

  if "errors" in result:
    raise newException(ValueError):
      &"Invalid query, server response:\n{pretty(result)}"

  else:
    # Unpack the data
    result = result["data"]

proc getPull(gh: GithubCli): Option[Pull] =
  ## Get the PR corresponding to the repo at the current directory
  let prIdCall = capture(
    "gh", "pr", "view",
    "--json", "id"
  )

  if prIdCall.exitcode == 0:
    let id = getStr parseJson(prIdCall.output)["id"]

    let js = gh.graphql(%*{ "id": id }):
      dedent"""
      query pr($id: ID!) {
        node(id: $id) {
          ... on PullRequest {
            title
            body
            number

            baseRepository {
              nameWithOwner
            }
            baseRefOid
          }
        }
      }
      """

    result = some Pull(
      targetRepo: getStr js["node"]["baseRepository"]["nameWithOwner"],
      number: getInt js["node"]["number"],
      title: getStr js["node"]["title"],
      body: getStr js["node"]["body"],
      baseCommit: getStr js["node"]["baseRefOid"]
    )

proc getGitAuthorship(): string =
  ## Obtain the user authorship information. This is used to filter authors to
  ## be placed in `Co-authored-by`.
  ##
  ## Returns a valid `Author <email>` string if the information can be retrieved,
  ## an empty string otherwise.
  # The ordering can be found in "COMMIT INFORMATION" section in git-commit(1)
  var name = getEnv("GIT_AUTHOR_NAME")

  if name == "":
    let call = capture("git", "config", "--get", "author.name")
    if call.exitcode == 0:
      name = call.output.strip()
  if name == "":
    let call = capture("git", "config", "--get", "user.name")
    if call.exitcode == 0:
      name = call.output.strip()
  if name == "":
    # If it is still empty, we don't know where to get this information
    return

  var email = getEnv("GIT_AUTHOR_EMAIL")

  if email == "":
    let call = capture("git", "config", "--get", "author.email")
    if call.exitcode == 0:
      email = call.output.strip()
  if email == "":
    let call = capture("git", "config", "--get", "user.email")
    if call.exitcode == 0:
      email = call.output.strip()
  if email == "":
    # If it is still empty, we don't know where to get this information
    return

  result = &"{name} <{email}>"

proc doSquash(gh: GithubBackend): bool =
  ## Perform the squash, returns false on failure
  let prOpt = gh.getPull
  if prOpt.isNone:
    stderr.writeLine(
      &"{getCurrentDir()}: not a git repository",
      " or does not have any PR associated with it"
    )
    return false

  let pr = get prOpt
  stdout.write pr

  stdout.writeLine "Pulling from remote"
  exec("git", "pull", "--ff-only")

  let commitCount = block:
    let call = capture(
      "git", "rev-list", "--count", &"{pr.baseCommit}..HEAD"
    )

    if call.exitcode != 0:
      echo "Could not get the commit count: ", call.error
      return

    parseInt:
      strip call.output

  if commitCount <= 1:
    echo "You have less than 2 commits in the branch, no squashing required!"
    return true

  let coAuthors = block:
    let authorsCall = capture(
      "git", "log",
      # This format specifier obtain all commit authors and co-authors and
      # present them in `Name <Email>` format
      "--format=%an <%ae>%+(trailers:key=Co-authored-by,valueonly)",
      &"{pr.baseCommit}..HEAD"
    )

    if authorsCall.exitcode != 0:
      echo "Could not get PR authors: ", authorsCall.error
      return

    let mainAuthor = getGitAuthorship()
    collect(newSeq):
      for author in authorsCall.output.splitLines:
        # Skip empty authors
        if author == "":
          continue
        # Skip the main author
        if author == mainAuthor:
          continue

        author

  var commitMsg = pr.toCommitMsg()
  if coAuthors.len > 0:
    commitMsg.add "\n"

    for author in coAuthors:
      commitMsg.add "\n"
      commitMsg.add &"Co-authored-by: {author}"

  echo "Creating the squash commit with the following message:"
  echo "---"
  echo commitMsg
  echo "---"

  let needGpg = block:
    let call = capture(
      "git", "config", "--get", "commit.gpgSign"
    )

    if call.exitcode != 0:
      echo "Could not get commit signing setting: ", call.error
      return

    call.output.strip() == "true"

  let commitCall = capture(
    "git", "commit-tree", "-p", pr.baseCommit, "HEAD^{tree}",
    input = some commitMsg
  )

  if commitCall.exitcode != 0:
    echo "Could not create the squash commit: ", commitCall.error
    return

  let squashed = commitCall.output.strip()
  echo "Created squash commit: ", squashed

  let branchName = block:
    let call = capture(
      "git", "branch", "--show-current"
    )

    if call.exitcode != 0:
      echo "Could not get current branch name: ", call.error
      return

    strip call.output

  let squashBranch = &"prsquash/{branchName}"
  echo &"Creating {squashBranch} from squash commit {squashed}"
  exec("git", "branch", "-f", squashBranch, squashed)

  let (pushRemote, pushRef) = block:
    let call = capture(
      "git", "for-each-ref", "--format=%(push:remotename)%00%(push)", &"refs/heads/{branchName}"
    )
    if call.exitcode != 0:
      echo "Could not obtain the remote to push to: ", call.error
      echo "Typically this would mean that you did not configure an upstream",
           " for the current branch. To push the squashed commit, run: ",
           quoteShellCommand([
             "git", "push", "--force-with-lease", "<push remote>", &"{squashBranch}:<remote branch>"
           ]),
           " with the correct parameters substituted in"

      return false

    let remoteInfo = call.output.strip.split({'\0'})

    (remoteInfo[0], remoteInfo[1].dup(removePrefix(&"refs/remotes/{remoteInfo[0]}/")))

  echo &"Force-pushing {squashBranch} to {pushRef}"
  exec("git", "push", &"--force-with-lease", &"{pushRemote}", &"{squashBranch}:{pushRef}")

  result = true

proc main() =
  block dispatch:
    let gh = GithubCli()
    if gh.available:
      if not doSquash(gh):
        quit QuitFailure

      break dispatch

    stderr.writeLine:
      "Error: one of the following tool must be installed: gh (Github CLI)"

when isMainModule: main()
