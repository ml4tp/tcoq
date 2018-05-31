# TCoq: Traced Coq 

Traced Coq is a version of Coq 8.6.1 that outputs the proof states of proofs as a parse-able data structure. For an example of parsing the format, see the (GamePad project)[https://github.com/ml4tp/gamepad].


## Installation

1. Configure tcoq.
   ```
   ./setup_tcoq.sh
   ```
2. Build tcoq. This takes roughly 10 minutes.
   ```
   ./build_tcoq.sh
   ```
   This procedure will generate a `build.log` file and `time.log` file in the current directory. The binaries will be placed in `./build`
	

## Usage

You can use TCoq like any other version of (Coq)[https://coq.inria.fr/].


## Modified files

1. printing/ptcoq.ml
2. ltac/tacinterp.ml
3. plugins/ssrmatching/ssrmatching.ml4
4. ltac/profile_ltac.mli
5. stm/stm.ml
