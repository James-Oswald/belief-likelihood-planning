

def chdir (newdir : System.FilePath) : IO UInt32 := do
  let PID <- IO.Process.getPID
  let cmd :=
    "gdb -q <<EOF\nattach " ++ toString PID ++
    "\ncall (int) chdir(\"" ++ newdir.toString ++
    "\")\ndetach\nquit\nEOF"
  let proc <- IO.Process.spawn {
    cmd := "bash"
    args := #["-c", cmd]
    stdout := IO.Process.Stdio.null
    stderr := IO.Process.Stdio.null
  }
  IO.Process.Child.wait proc

def main : IO Unit := do
  let cwd <- IO.currentDir
  IO.println cwd
  IO.FS.createDir "subdir"
  let _ <- chdir "subdir"
  --We are now in subdir
  let cwd <- IO.currentDir
  IO.println cwd
  let _ <- chdir ".."
  --We are now back in the starting directory
  let cwd <- IO.currentDir
  IO.println cwd
  IO.FS.removeDir "subdir"
