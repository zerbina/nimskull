import
  front/[
    options,
    msgs
  ],
  ast/[
    lineinfos,
  ],
  std/[
    os,
    tables,
    strutils
  ]

proc formatPath*(conf: ConfigRef, path: string): string =
  ## Format absolute path for reporting
  if path in conf.m.filenameToIndexTbl:
    # Check if path is registered in filename table index - in that case
    # formatting is done using `FileInfo` data from the config.
    let id = conf.m.filenameToIndexTbl[path]
    result = toFilenameOption(conf, id, conf.filenameOption)

  else:
    # Path not registered in the filename table - most likely an
    # instantiation info report location
    when compileOption"excessiveStackTrace":
      # instLoc(), when `--excessiveStackTrace` is used, generates full
      # paths that /might/ need to be filtered if `--filenames:canonical`.
      const compilerRoot = currentSourcePath().parentDir().parentDir()
      if conf.filenameOption == foCanonical and
         path.startsWith(compilerRoot):
        result = path[(compilerRoot.len + 1) .. ^1]

      else:
        result = path

    else:
      result = path

proc formatPath*(conf: ConfigRef, idx: FileIndex): string =
  conf.toFilenameOption(idx, conf.filenameOption)
