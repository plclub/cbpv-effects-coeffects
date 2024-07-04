# Debugging Notes

## Running QEMU without a Display

You can start the VM without the console display like so:

```
$ sudo sh start.sh -display none
```

Then connect to it via SSH.

```
$ ssh -p 5555 artifact@localhost
```

## OSX

- If you are running OSX Catalina and have an old version of QEMU already
  installed then you may see a black screen when the VM starts. One AEC member
  had this problem and resolved it by upgrading to the current version of QEMU.

- There is a known issue with the hypervisor entitlements for QEMU on
  maxOS >= 11.0 as described at

  https://www.arthurkoziel.com/qemu-on-macos-big-sur/

  Sandro Stucki has provided the accompanying shell script,
  `fix-qemu-macos.sh`, which can be used to fix the issue.

## Linux

### Problem: KVM Kernel Module Does Not Load

Symptom:
```
$ sh start.sh
Linux host detected.
Could not access KVM kernel module: No such file or directory
qemu-system-x86_64: failed to initialize KVM: No such file or directory
```

Check whether the `kvm-intel` or `kvm-amd` module is loading correctly.
You might get:
```
$ sudo modprobe kvm-intel
modprobe: ERROR: could not insert 'kvm_intel': Operation not supported
```

Check the dmesg log to see if virtualization has been disabled in the BIOS:
```
$ dmesg | tail
...
[  848.697757] kvm: disabled by bios
```

Check your BIOS configuation for a setting like "Intel Virtualization
Technology" and ensure that it is enabled.

### Problem: Virtualization Still Does Not Work

If the KVM virtualization system still doesn't work then you can use plain
emulation via the Tiny Code Generator. This will be slower, but otherwise has
the same functionality.

```
$ sudo sh start.sh -accel tcg
```

## Windows

On (old) Windows 8, following the instructions from README.md is known to fail
with the following:

```
c:\...\qemu-system-x86_64: Could not load library WinHvPlatform.dll.
c:\...\qemu-system-x86_64: failed to initialize WHPX: Function not implemented
```

An AEC member with a Windows 8 machine was able to get it the image working by
changing the .bat file to use the HAXM virtualization system instead of WHPX.

1. install the latest haxm
2. make sure the hyper-v feature is off
3. change the -accel flag in the .bat file to hax

## Coq

### Problem: Installing Coq via Opam Fails

Debian may use an old version of `opam` with a non-working dependency solver.
This causes `opam switch init` to fail with error

```
ERROR: grounder returned with non-zero exit status
```

An AEC member who tested the image encountered the problem when trying to
install Coq via the instructions given at

https://github.com/coq/coq/wiki/Installation-of-Coq-on-Linux

The full reported error was:

```
> opam switch create 5.2.0
[ERROR] Solver failed: "/usr/bin/aspcud /home/artifact/.opam/log/solver-in-546-5f1023 /home/artifact/.opam/log/solver-out-546-58c514
        -count(removed),-sum(request,version-lag),-count(down),-sum(solution,version-lag),-count(changed)" exited with code 1 "ERROR: grounder returned with non-zero exit status"
```

[This GitHub issue](https://github.com/ocaml/opam/issues/3827) advises to opt
for a different solver:

```
rm -rf ~/.opam
sudo apt install mccs
opam switch create 5.2.0 --solver=mccs
```
