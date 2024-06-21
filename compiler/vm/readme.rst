Built-in VM evaluation. This directory contains modules that implement
the VM for running code at compile-time, for the NimScript target, and for
the standalone VM target.

The core VM is implemented by the ``vm``, ``vm_enums``, ``vmdef``, ``vmalloc``,
``vmchecks``, and ``vmobjects`` modules. These modules can be used without
pulling in compiler modules.