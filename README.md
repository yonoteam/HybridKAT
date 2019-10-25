# Hybrid KAT, differential Hoare Logic and differential Refinement Calculus

The Isabelle files can be found in the KAT folder. The relevant files for the paper are 
KAT_rKAT_Examples_ndfun.thy, KAT_rKAT_exuclid_Examples_ndfun.thy and all those that they import.

The files run smoothly with [Isabelle2019 (August 2019)](https://isabelle.in.tum.de/) (August 2019). 
Moreover, they all depend on various [AFP](https://www.isa-afp.org/) entries: 
* [Verification Components for Hybrid Systems](https://www.isa-afp.org/entries/Hybrid_Systems_VCs.html),
* [Transformer Semantics](https://www.isa-afp.org/entries/Transformer_Semantics.html), and
* [Isabelle UTP](https://www.cs.york.ac.uk/circus/isabelle-utp/publications.html).

You need all of those entries if you are to run our verification components. Alternatively, if you are 
only interested in looking at the proofs, we include a ProofDocument.pdf in the KAT folder of the repository.

The theory stack is enormous, hence its verification takes more than 40 minutes. This is the reason why we 
recommend building a heap that pre-loads the stack. In order to do this in a Unix system, if all the
dependencies have already been installed, follow the steps below:

1. Open Terminal.
2. Add the Isabelle bin directory to your PATH variable, e.g. $ export PATH=$PATH:/.../Isabelle2019.app/Isabelle/bin
(replace the ... with your actual path to the Isabelle installation directory).

3. If you installed all of the AFP, you will need to go to its contents, i.e. "$ cd /Users/.../afp/thys" 
and delete the [UTP entry](https://www.isa-afp.org/entries/UTP.html) from its ROOTS file to avoid clashes with 
[Isabelle UTP](https://www.cs.york.ac.uk/circus/isabelle-utp/publications.html).

4. Then execute: $ isabelle build -d /Users/.../utp/utp-main/ -d /Users/.../afp/thys -b UTP-Hybrid-Imports
5. Wait for the build to finish, go for tea or coffee.
6. To launch Isabelle, just type $ isabelle jedit -d /Users/.../utp/utp-main/ -d /Users/.../afp/thys -l UTP-Hybrid-Imports

NOTE: The build command, is only necessary once. After that, you just need to do steps 1, 2 and 6.

