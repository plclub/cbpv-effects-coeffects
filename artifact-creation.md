# Steps to recreate the artifact environment
This section describes how to recreate the artifact environment from
the official [Arch Linux VM image](https://gitlab.archlinux.org/archlinux/arch-boxes/).

The first step uses the package manager `pacman` to install `opam` and is usually only applicable to Arch-based
distributions. The rest of the steps are mostly distribution-agnostic
and can be followed if you have a working installation of `opam`.

The steps involving copying source files to the VM through the
`scp` command can be skipped if the environment is to be created on
the host machine where source files of the artifact are already
available.

Here are the package versions that are known to work:

- opam 2.1.6

### Install opam and other develop tools
```sh
sudo pacman -Syu
sudo pacman -S opam git unzip make patch gcc
```

If the installation causes a kernel upgrade, you might want to reboot
the VM first before proceeding to the next steps.

```sh
sudo reboot
```

### Copy the artifact source to the VM
On the host machine, run the following command:
```sh
scp -P 5555 cbpv_artifact.zip arch@localhost:~/
```

You can unzip the artifact on the guest VM:
```
unzip cbpv_artifact.zip
```

The `coq-switch` file contained in the unzipped directory will be
used in the next step to create an opam switch with the dependencies
properly installed.

### Install Coq and ott
After a fresh installation of `opam`, you need to run the
following command to initialize it.
```sh
opam init -a --bare
```

Once `opam` is initialized, the next step is to import the switch
configuration used to build the Rocq/Coq development.

First, switch to the directory containing the Rocq development:
```sh
cd ~/cbpv-effects-coeffects
```

Here you can find a file named
[coq-switch](coq-switch). This file records the packages and their
versions that we use to verify our development.

You can run the following command to
create a switch named `cbpv` with Rocq (and the required
libraries) installed: 
```sh
opam switch import coq-switch --switch cbpv --repositories=coq-released=https://coq.inria.fr/opam/released,default=https://opam.ocaml.org
opam switch cbpv
eval $(opam env)
```
Note: the `opam switch import` command took around 12 minutes to
execute on a machine with 13th Gen Intel® Core™ i7.

To check whether the installation was successful, run the following
command and you should see the help message for Rocq:
```sh
coqc --help
```
# Autosubst2
If you want to regenerate the syntax.v files, you will need to clone Autosubst2 from [Github](https://github.com/uds-psl/autosubst2/tree/main) and build it using the instructions in the README.md file.
The syntax is already generated, so that step is not necessary to validate the proofs.

This completes the construction of the VM. You can now follow the
instructions from [artifact-overview](artifact-overview) to verify the
Rocq development.
