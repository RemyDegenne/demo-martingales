# Probability in Mathlib

This repository contains an introduction to probability in Lean and Mathlib.

## Usage
Install [Lean 4](https://lean-lang.org/install/). Then, clone the repository and run the following command in the root directory:

```bash
cd src
lake exe cache get
lake build
```
Now you can explore the proof using your favorite editor with Lean support, such as [VSCode](https://code.visualstudio.com/) with the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4). Your editor should be open in the `src` directory.

## Documentation
The documentation is available [here](https://gaetanserre.fr/doc/LipoCons/). To build it, clone the repository and run the following command in the root directory:

```bash
cd src
lake exe cache get
lake build
cd ..
./build_manual.sh
```
The documentation will be generated in the `doc` directory. You will need a local web server to view the documentation. You can use Python's built-in HTTP server:

```bash
cd doc
python3 -m http.server
```
and open your web browser at `http://localhost:8000`.