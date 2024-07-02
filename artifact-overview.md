Artifact accompanying "Effects and Coeffects in Call-by-Push-Value"

## Introduction

This artifact accompanies the paper "Effects and Coeffects in
Call-by-Push-Value" and contains mechanically verified proofs of the major
theorems in the paper, developed using the Coq/Rocq proof assistant.

  We have included the publication version of the paper with the artifact. This contains hyperrefs to the public github repository
   containing this code. For space reasons, some language features that 
   are part of the artifact are not included in this paper.
       
  TODO
  We have also included an appendix containing the full rules, taken from an extended version of our paper that more closely corresponds to the artifact. This version
   includes references to definitions and theorems presented as footnotes so
   they will be available even when the document is printed. It will be uploaded to arXiv https://arxiv.org/abs/2311.11795 and will replace the
   current version at that link.
       
## Dependencies

No specific hardware requirements.

## Getting Started Guide

To validate the proofs through the VM, first install `qemu` following the [QEMU Installation
instructions](#installation). Next, start up the VM and
access the VM through `ssh` following the [Startup](#startup)
instructions. If done correctly, the terminal should display the
following command line prompt:
```sh
[arch@archlinux ~]$
```

Note: When starting up the VM, you have the option to set the environment
variable `QEMU_MEM_MB` to specify the number of megabytes allocated to the
VM's memory. By default, the VM launches with a single CPU and 4096MiB of
memory. You can add more cores to the VM by passing the `-smp n` flag to the
startup script where `n` should be replaced by the number of cores allocated
to the VM. If you intend to use more than 4 cores, you should increase the
memory size because running multiple jobs in parallel requires more memory
space.


## Evaluating the Artifact Functionality

The proofs can be verified by running the following in the terminal
  from the top-level directory:
```sh
make clean
make
```
Optionally, you can pass the `-j[jobs]` flag to `make` where `[jobs]`
is replaced by an integer representing the number of the jobs
that you want to run in parallel. This can reduce the build time
significantly. However, since the VM by default has only 4 GiB of memory,
running too many jobs simultaneously can cause the `coqc` compiler to
be killed. If that happens, you should decrease the number you pass to `-j`.

Note: On a Linux machine with Ryzen 5700x, the entire development
takes TODO to compile with `make -j4`.

A successful compilation should produce the following output:

```
{ echo "-R . cbpv " ; ls autosubst2/*.v common/*.v general/*.v */CBPV/*.v */CBV/*.v */CBN/*.v ; } > _CoqProject
coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module,-notation-overridden' -f _CoqProject -o CoqSrc.mk
make -f CoqSrc.mk
make[1]: Entering directory '/Users/sweirich/github/coq/cbpv-coeffects'
COQDEP VFILES
COQC autosubst2/axioms.v
COQC autosubst2/fintype.v
COQC common/fin_util.v
COQC common/coeffects.v
COQC common/coeffect_renaming.v
COQC common/effects.v
COQC common/junk_axioms.v
COQC common/resource_axioms.v
COQC effects/CBN/syntax.v
COQC effects/CBN/typing.v
COQC effects/CBPV/syntax.v
COQC effects/CBPV/typing.v
COQC effects/CBPV/renaming.v
COQC effects/CBN/translation.v
COQC effects/CBN/proofs.v
COQC effects/CBPV/semantics.v
COQC effects/CBPV/semtyping.v
COQC effects/CBPV/soundness.v
COQC effects/CBV/syntax.v
COQC effects/CBV/typing.v
COQC effects/CBV/translation.v
COQC effects/CBV/proofs.v
COQC full/CBPV/syntax.v
COQC full/CBPV/typing.v
COQC full/CBPV/renaming.v
COQC full/CBN/syntax.v
COQC full/CBN/typing.v
COQC full/CBN/translation.v
COQC full/CBN/proofs.v
COQC full/CBPV/semantics.v
COQC full/CBPV/semtyping.v
COQC full/CBPV/junk.v
COQC full/CBPV/soundness.v
COQC full/CBV/syntax.v
COQC full/CBV/typing.v
COQC full/CBV/translation.v
COQC full/CBV/proofs.v
COQC full/CBV/semantics.v
COQC general/syntax.v
COQC general/semantics.v
COQC general/typing.v
COQC general/semtyping.v
COQC general/soundness.v
COQC resource/CBPV/syntax.v
COQC resource/CBPV/typing.v
COQC resource/CBPV/renaming.v
COQC resource/CBN/syntax.v
COQC resource/CBN/typing.v
COQC resource/CBN/translation.v
COQC resource/CBN/proofs.v
COQC resource/CBPV/semantics.v
COQC resource/CBPV/semtyping.v
COQC resource/CBPV/soundness.v
COQC resource/CBV/syntax.v
COQC resource/CBV/typing.v
COQC resource/CBV/translation.v
COQC resource/CBV/proofs.v
make[1]: Leaving directory '~/cbpv-coeffects' TODO
```

## Evaluating the Artifact Reusibility

Checking the proofs requires the Coq Proof Assistant, version 8.19.2. 

Extending the development with any changes to the syntax requires the Autosubst 2 tool to regenerate the syntax
files. All syntax files needed for the languages described in the paper are
already included in the distribution and do not need to be recreated.  (The
commands `make` and `make clean` do not regenerate or remove these files
respectively; `make fullmake` and `make fullclean` will do so and so require
Autosubst 2.)

Detailed instructions for replicating the environment 
are available in a [separate file](artifact-creation.md).



## Contents

- autosubst2
  files distributed with Autosubst 2

- common
  files used by all subsections

- effects
  results in Section 2 (Effects)

- general
  results in Section 3 (Coeffects, Version 1)

- resource
  results in Section 4 (Coeffects, Version 2)

- full
  results in Section 5 (Combined)

## Required axioms

- Axioms required by autosubst  (`autosubst2/axioms.v`)
- Axiomatization of effects (`common/effects.v`)
- Axiomatization of coeffects (`common/coeffects.v`)
- Additional resource-tracking-specific axiomatization of coeffects
   (`common/resource_axioms.v`)
- Axiomatization of discardable effects (`common/junk_axioms.v`)


## QEMU Installation instructions

QEMU is a hosted virtual machine monitor that can emulate a host processor
via dynamic binary translation. On common host platforms QEMU can also use
a host provided virtualization layer, which is faster than dynamic binary
translation.

QEMU homepage: https://www.qemu.org/

### Installation

#### OSX
``brew install qemu``

#### Debian and Ubuntu Linux
``apt-get install qemu-kvm``

On x86 laptops and server machines you may need to enable the
"Intel Virtualization Technology" setting in your BIOS, as some manufacturers
leave this disabled by default. See Debugging.md for details.


#### Arch Linux

``pacman -Sy qemu``

See the [Arch wiki](https://wiki.archlinux.org/title/QEMU) for more info.

See Debugging.md if you have problems logging into the artifact via SSH.


#### Windows 10

Download and install QEMU via the links at

https://www.qemu.org/download/#windows.

Ensure that `qemu-system-x86_64.exe` is in your path.

Start Bar -> Search -> "Windows Features"
          -> enable "Hyper-V" and "Windows Hypervisor Platform".

Restart your computer.

### QEMU Startup

The base artifact provides a `start.sh` script to start the VM on unix-like
systems and `start.bat` for Windows. Running this script will open a graphical
console on the host machine, and create a virtualized network interface.
On Linux you may need to run with `sudo` to start the VM. 

Once the VM has started you can login to the guest system from the host.
Whenever you are asked for a password, the answer is `arch`. The default
username is `arch`.

```
$ ssh -p 5555 arch@localhost
```

You can also copy files to and from the host using scp.

```
$ scp -P 5555 arch@localhost:somefile .
```

### Shutdown

To shutdown the guest system cleanly, login to it via ssh and use

```
$ sudo shutdown now
```

### Reset the state of the VM

If you corrupted the VM state by accident, you can simply reset the VM
state through QEMU's snapshot feature.
```sh
qemu-img snapshot -a initial-state disk.qcow2
```

### QEMU troubleshooting

If the artifact needs lots of memory, you may need to increase the value
of the `QEMU_MEM_MB` variable in the `start.sh` script.
