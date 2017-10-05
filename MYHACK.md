# Description

1. Making sure that I can build Coq 8.6.1 from source.
2. Hacking `coqchk` to dump out proof terms.

```
git remote add origin ssh://git@bitbucket.org/dan-e-huang/coq.git
```

```
git push -u myrepo deh
```

# Instructions

1. The open source version of Coq is in `~/Documents/research/pnh/coq`.

    ```
    cd ~/Documents/research/pnh/coq
    ```

2. Configure `./configure`

	```
	/Users/dehuang/Documents/research/pnh/coq/build/bin
	/Users/dehuang/Documents/research/pnh/coq/build/lib/coq
	/Users/dehuang/Documents/research/pnh/coq/build/extra
	/Users/dehuang/Documents/research/pnh/coq/build/share/coq
	/Users/dehuang/Documents/research/pnh/coq/build/share/man
	/Users/dehuang/Documents/research/pnh/coq/build/share/doc/coq
	/Users/dehuang/Documents/research/pnh/coq/build/share/emacs/site-lisp
	/Users/dehuang/Documents/research/pnh/coq/build/share/texmf/text/latex/misc
	```

3. Make the modified `coq`. The binaries are currently configured to be installed to `~/Documents/research/pnh/coq/build/bin`.

    ```
    make -j4
    ```

4. You should now be able to use the modified `coq`. 

5. Example `myconfig.sh` file. To use this version of coq, make sure to source this configuration file.

	```
	export PATH="/Users/dehuang/Documents/research/pnh/coq/build/bin":$PATH
	export COQ_MK="/Users/dehuang/Documents/research/pnh/coq/build/bin/coq_makefile"
	export COQBIN="/Users/dehuang/Documents/research/pnh/coq/buildbin/"
	```
