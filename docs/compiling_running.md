# Compiling
Go to the root directory of the code, and `make all`, this would compile the program into an executable file `sctl` in the same directory.

**Compiling Environment Requirements**

1. OCaml is installed, and packages yojson and cuddidl are installed via opam;
2. [CADP](http://cadp.inria.fr/) is installed, and the corresponding environment variables are successfully set up according to the README files of CADP.

# Running

See ```sctl --help```.

**In practice, SCTLProV runs faster (not very much) when the `-output` option is not specified. 
So if efficiency is your main concern, do not use the output option.
When option `-bdd` is specified, SCTLProV usually consumes more time and less memory space than not using the `-bdd` option.**

# Benchmarks
See the file `benchmarks.md`', which is a description of the benchmarks in the `benchmarks` folder.


# Visualization
We also wrote an visualization tool for the visualization of proof trees, called VMDV, which is also avaliable on [this website](https://github.com/terminatorlxj/vmdv). The proof tree produced by SCTLProV can be visualized in 3D space by VMDV. Interested readers may refer to the README file of VMDV for further usage information.

