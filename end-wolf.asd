(asdf:defsystem #:end-wolf
  :depends-on (:iterate :static-vectors :lparallel)
  :serial t
  :components
  ((:file "end-wolf")))
