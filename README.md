isabelle-opentheory
===================

This is a proof of concept demonstrating the import of OpenTheory articles into Isabelle.
It has been tested with Isabelle2017.

Authors
-------

* Brian Huffman: initial implementation, up to Isabelle2011-1
* Japheth Lim: updates to Isabelle2015
* Ramana Kumar: updates to Isabelle2016, tweaks
* Maksym Bortin: examples for OpenTheory, updates to Isabelle2017
* Lars Hupel: tweaks

Setup
-----

Loading this session into Isabelle/jEdit or building it in batch mode requires some `*.art` files to be present.
The script `./get_arts` downloads and processes them through OpenTheory.
It requires a working `opentheory` executable and Internet connection.

Afterwards, either build the `Open_Theory` session or open it in Isabelle/jEdit.


Known Issues
------------

* The import of OpenTheory articles is single-threaded and hence rather slow.
* None of the existing code is properly integrated into Isabelle (or jEdit).
  In particular, there is no `opentheory` command; you have to call the ML function `OpenTheory.read_article`.
  There is also no markup for article files, nor are changes to the files detected in batch build or interactive mode.
* The `get_arts` script requires the `opentheory` executable.
  The ML code is not able to fetch the `*.art` files itself.
  Even though [a component](https://github.com/isabelle-prover/opentheory-component) porting OpenTheory to Isabelle/ML exists, that is not used.
* The `get_arts` script crudely greps the theory sources for mentioned `*.art` files and downloads them accordingly.
