#!/usr/bin/env python3

""" Build system of the compiler

Add the following to zshrc or bachrc to have the convenient `$ x` instead of
`$ ./x`, or `$ ../x`

x() {
    local dir="$PWD"
    local target="x"

    while [ "$dir" != "/" ]; do
        if [ -x "$dir/$target" ]; then
            "$dir/$target" "$@"
            return $?
        elif [ -f "$dir/$target" ]; then
            echo "Found '$target' at $dir/$target but it's not executable." >&2
            return 126
        fi
        dir="$(dirname "$dir")"
    done

    echo "Error: '$target' not found in current or parent directories." >&2
    return 127
}
"""

import subprocess as sp
import sys
from pathlib import Path

def usage():
    return "Usage: ./b <command>, type help to see all the commands"

def main():
    args = sys.argv

    if len(args) <= 1:
        print(usage())
        return

    remaining_args = args[2:]
    match args[1]:
        case "run":
            cmd_run(remaining_args)
        case "test":
            cmd_test(remaining_args)
        case "build":
            cmd_build()
        case "watch":
            cmd_watch(remaining_args)
        case "new-code":
            cmd_new_code(remaining_args)
        case "help" | "h":
            cmd_help()
        case _:
            print(usage())
            return

def cmd_run(args: list[str]):
    res = build(True, "muonc")

    if res.returncode != 0:
        exit(res.returncode)

    run_cmd = ["target/debug/muonc", "--color=always"] + args
    res = sp.run(run_cmd, env = {"RUST_BACKTRACE": "full"})

    if res.returncode != 0:
        exit(res.returncode)

def cmd_test(args: list[str]):
    exit("ERROR: no testing harness for now!")

    res = build(True, "muonc")

    if res.returncode != 0:
        exit(res.returncode)

    res = build(True, "muontests")

    if res.returncode != 0:
        exit(res.returncode)

    run_cmd = ["target/debug/muontests"] + args
    res = sp.run(run_cmd)

    if res.returncode != 0:
        exit(res.returncode)

def cmd_build():
    build(False, "muonc")

def build(quiet: bool, bin: str) -> sp.CompletedProcess[bytes]:
    if quiet:
        args = ["cargo", "build", "-q", "--bin", bin]
    else:
        args = ["cargo", "build", "--bin", bin]

    return sp.run(args)

def cmd_watch(args: list[str]):
    if len(args) == 0:
        sp.run(["cargo", "watch"])
    else:
        cmd = ["cargo", "watch", "--shell", " ".join(args)]
        sp.run(cmd)

def cmd_new_code(args: list[str]):
    if len(args) != 2:
        print("Usage: ./b new-code <error|warn> <code>")
        return

    kind = args[0]
    code = args[1]

    if len(code) != 4:
        print("ERROR: the code must be 4 character long like that: `0001`")
        return

    if kind == "error":
        prefix = "E"
    elif kind == "warn":
        prefix = "W"
    else:
        print("ERROR: first argument must be either 'error' or 'warn'")
        return

    path = Path(f"src/doc/{prefix}{code}.md")
    content = f"""# {kind.capitalize()} `{prefix}{code}`

<!-- TODO: make the error message -->
"""

    path.parent.mkdir(parents=True, exist_ok=True)

    try:
        path.write_text(content, encoding="utf-8")
    except FileExistsError:
        print(f"ERROR: file already exists: {path}")
        return

    print(f"Created {path}")

def cmd_help():
    print("""\
Development utility for the Muon compiler

Usage: ./b

Commands:
    build               Build the muon compiler
    watch [cmd]         Watch for changes in source code and runs [cmd] if
                        provided or defaults to `cargo check`
    run  [ARGS...]      Runs the compiler with the given arguments, rebuild it
                        quietly if needed
    test [ARGS...]      Runs the compiler tests and forwards it the following
                        arguments
    new-code KIND CODE  Creates a new error/warning doc file
                        KIND must be `error` or `warn`
                        Examples:
                            ./b new-code error 0012
                            ./b new-code warn 0003
    help, h             Prints this message\
""")

if __name__ == "__main__":
    main()
