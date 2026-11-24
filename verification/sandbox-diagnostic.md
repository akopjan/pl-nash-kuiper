# Sandbox environment diagnostic

The standard Comparator invocation is recorded in
`comparator-sandbox-final.json` and `comparator-sandbox-final.log`. It exits
before building the submitted project, with:

```text
bwrap: Failed to mount tmpfs: No such file or directory
error: Child exited with 1
Resolving dependencies
```

The pinned toolchain's `Lake/CLI/Check.lean` constructs a sandbox with
read-only `/` and temporary filesystems at `/home`, `/root`, `/run/user`,
and `/tmp`. Filesystem inspection in this workspace found `/home` but
reported `ENOENT` for `/root`, `/run`, `/run/user`, and `/tmp`.

A separate diagnostic mounted a temporary filesystem at an existing scratch
directory and attempted to execute only `/usr/bin/true`, retaining
`--unshare-all`, `--die-with-parent`, and `--new-session`. It did not run any
project code or change the Comparator command. Bubblewrap 0.12.0 then failed
with:

```text
bwrap: loopback: Failed to create NETLINK_ROUTE socket: Operation not permitted
```

Thus creating a missing working directory alone would not make the standard
sandbox available: this environment also denies an operation needed to
initialize its network namespace. No sandbox setting, namespace restriction,
host security setting, or toolchain source was disabled or changed. The
read-only export comparison and independent kernel replay remain separately
identified proof checks.
