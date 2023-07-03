# Chemical Theories in Lean
The repository is a collection of Lean documentation created to formalize theorem statements and proofs in chemical sciences and engineering, as described in [Formalizing Chemical Theory using the Lean Theorem Prover](https://arxiv.org/abs/2210.12150).

The paper and its proofs are written in Lean 3. We have created a [static branch](https://github.com/ATOMSLab/LeanChemicalTheories/tree/static-branch_2023-06-18) of our repository where all the proofs are in the state as it was on 2023/06/22 and aligns with the code referenced in the paper. 
The code is compatible with `Lean` version `3.51.1` and `mathlib` commit `2ad3645af9effcdb587637dc28a6074edc813f9`. 
The proofs have been reproduced without errors on both MacOS and Windows platforms.

Moving forward, all of our upcoming proofs will be written in the latest version of Lean, which is [Lean 4](https://github.com/leanprover/lean4). 
Some of these proofs might be updated to remain in line with new releases of both `Lean` and `mathlib`. For those looking to access the most current version, it can be found on the main branch, which is also hosted at https://atomslab.github.io/LeanChemicalTheories/ using [doc-gen](https://github.com/ATOMSLab/doc-gen/tree/master). 


## Instructions to run this project
To download the project after installing `Lean` (see instructions below), run `leanproject get ATOMSLab/LeanChemicalTheories` in the terminal window: 

To confirm the completeness and accuracy of the proofs, run `bash ./test` in the root directory of the project.

If everything builds successfully, the script will display `Result: Success`.

## Instructions to install `Lean`, `mathlib`, and its supporting tools
These instructions are adapted from the [Lean 3 community website](https://leanprover-community.github.io/lean3/get_started.html) which has been archived 
and is currently being deprecated. 

Lean itself doesn't depend on much infrastructure, but supporting tools needed by most users require `git`, `curl`, and `python3` 
(on Debian and Ubuntu also `python3-pip` and `python3-venv`). 

To run programs smoothly in the Lean Theorem Prover, we need to set up `Lean`, an editor that knows about `Lean` (VSCode is recommended), 
and `mathlib` (the standard library). Rather than installing Lean directly, the installation is handled through a small program 
called [`elan`](https://github.com/leanprover/elan) that automatically provides the correct version of Lean on a per-project basis.\
This is recommended for all users.

#### Linux

1. Install `elan`:
  In the terminal, run the command
      ```bash
      curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
      ```
  and hit enter when a question is asked. It will live in $HOME/.elan and add a line to $HOME/.profile.

2. Get `Visual Studio Code`:
   Next step is getting the lean editor, [VS Code](https://code.visualstudio.com/). 

  * Install and launch [VS Code](https://code.visualstudio.com/).
  * Install the `lean' extension (unique name `jroesch.lean`).
  * Verify Lean is working, for example by saving a file `test.lean` and entering `#eval 1+1`.
    A green line should appear underneath `#eval 1+1`, and hovering the mouse over it you should see `2`
    displayed.

3. Then we install a small tool called `leanproject` that which will handle updating mathlib according to the needs of your current project. We use
  [pipx](https://pipxproject.github.io/pipx/) to perform the installation.
      ```bash
      python3 -m pip install --user pipx
      python3 -m pipx ensurepath
      source ~/.profile
      pipx install mathlibtools
      ```  

#### Windows

1. We will need a terminal, along with some basic prerequisites.
   We recommend the use of `git bash` and not `msys2`, since installing the supporting tools (below) causes issues in `msys2`.

   Install [Git for Windows](https://gitforwindows.org/) (you may accept all default answers during installation).
   Then open a terminal by typing `git bash` in the Windows search bar.

2. Install `elan`:
   In the terminal, run the command:
       ```bash
       curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
       ```
   and hit enter when a question is asked.

   To make sure the terminal will find the installed files, run `echo 'PATH="$HOME/.elan/bin:$PATH"' >> "$HOME/.profile"`.
   Then close and reopen Git Bash.

4. Configure `Git`:
   Run `git config --global core.autocrlf input` in Git Bash
   Alternatively, you can set it to `false`. If it is set to `true`, you might run into issues when running `leanproject`.

5. Get `Scripts`:
   Then, at the terminal, run the command
    ```bash
    pip3 install mathlibtools
    ```
6. Get `VS Code`:
   * Install and launch [VS Code](https://code.visualstudio.com/).
   * Install the `lean' extension (unique name `jroesch.lean`).
   * Setup the default profile:
           * If you're using `git bash`, press `ctrl-shift-p` to open the command palette, and type
           `Select Default Profile`, then select `git bash` from the menu.
           * If you're using `msys2`, press `ctrl-comma` again to open the settings, and add two settings:
           ```text
           "terminal.integrated.shell.windows": "C:\\msys64\\usr\\bin\\bash.exe",
           "terminal.integrated.shellArgs.windows": ["--login", "-i"]
           ```
   * Restart VS Code.
   * Verify Lean is working, for example by saving a file `test.lean` and entering `#eval 1+1`.
    A green line should appear underneath `#eval 1+1`, and hovering the mouse over it you should see `2`
    displayed.

There is a [video walkthrough](https://www.youtube.com/watch?v=y3GsHIe4wZ4) of these instructions on YouTube. If you get stuck, please come to [the chat room](https://leanprover.zulipchat.com/) to ask for assistance.


#### Intel Macs

The fast way that will install Lean, with supporting tools `elan` and `leanpkg`, the supporting tool `leanproject` for Lean's mathematical library, as well as the code editor VS Code and its Lean plugin. Open a terminal and type:
    ```bash
    /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/leanprover-community/mathlib-tools/master/scripts/install_macos.sh)" && source ~/.profile
    ```

#### M1 Macs / Apple Silicon

Given that GitHub Actions does [not yet support builds on Apple ARM](https://github.com/actions/virtual-environments/issues/2187), installation of Lean is for the moment a bit more complex.

Specifically, `elan` – which is installed as part of the above instructions – will not be able to fetch Lean binaries on these devices if installed the normal way.

The following instructions are adapted from [Fedor Pavutnitskiy](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/M1.20Macs.3A.20Installing.20the.20Lean.203.20toolchain/near/262832039), and allow you to install elan through [Rosetta](https://developer.apple.com/documentation/apple-silicon/about-the-rosetta-translation-environment).

1. Open a new terminal window and install XCode Command Line Tools and Rosetta 2 using `xcode-select --install` and `softwareupdate --install-rosetta`.
   
2. We will install a second, separate x86 installation of Homebrew, which is easiest done by running a shell entirely using Rosetta 2. Do so by running `arch -x86_64 zsh`. The remainder of the commands below should be run from within this `x86`-running window, though once the steps have been completed, the installed tools will work in any future shell.
   
3. Install a second installation of Homebrew for `x86` with `/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"`. It will automatically install itself into a second location (`/usr/local`, rather than `/opt/`).
   
4. Follow the same steps described in [Controlled Installation for macOS](https://leanprover-community.github.io/install/macos_details.html) using the `brew` you just installed:
    ```
    /usr/local/bin/brew install elan-init mathlibtools
    elan toolchain install stable 
    elan default stable  
    ```
5. Install `VS Code` and the Lean extension via `brew install --cask visual-studio-code && code --install-extension jroesch.lean` (both the x86 and ARM versions of `brew` should work).

There is a [video walkthrough](https://www.youtube.com/watch?v=NOGWsCNm_FY) of these instructions on YouTube.
If you get stuck, please look into the [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/M1.20macs) for interim details and advice. If you have trouble, feel free to ask for help.
