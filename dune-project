(lang dune 3.3)

(name bitts)

(using menhir 2.1)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name bitts)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
   (ocaml (>= 4.13.1))
   (dune (>= 3.3))
   (sedlex (>= 2.5))
   (menhir (>= 20220210)))
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
