# COQ

- _Lernen Sie COQ Schritt für Schritt_

- SOURCES:

  - [Software Foundations](https://clarksmr.github.io/sf-lectures/textbook/lf/toc.html)
  - [COQ manual](https://coq.inria.fr/doc/V8.18.0/refman/)

- COMPILATION:
  - create a \_CoqProject file

    ```sh
     $> echo "-Q . PROJECTNAME" >> _CoqProject
    ```

  - with MakeFile

    ```sh
    $> coq_makefile -f _CoqProject -o Makefile *.v
    ```

  - without MakeFile

    ```sh
    $> coqc -Q . PROJECTNAME FILENAME.v
    ```
