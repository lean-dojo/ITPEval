;; Statement-only formalization of Logipedia corpus artifact
;; leibniz.sym_leibniz, catalog title "leibniz.sym_leibniz": for every type
;; and two elements of that type, Leibniz equality from the first element to
;; the second implies Leibniz equality from the second to the first. This file
;; contains no proof.

(in-package "ACL2")

;; The source definition forall P, P(x) -> P(y) is bidirectionally equivalent
;; to identity: identity transports every predicate, and the converse follows
;; by taking P(z) to mean z = x. ACL2 EQUAL therefore represents Leibniz
;; equality exactly, while this conservative interface retains arbitrary
;; source types and their carriers.

(defstub logipedia-leibniz-sym-member-p
  (a-type value)
  t)

(defun-sk logipedia-leibniz-sym-statement ()
  (forall (a-type x y)
    (implies
     (and
      (logipedia-leibniz-sym-member-p a-type x)
      (logipedia-leibniz-sym-member-p a-type y))
     (implies
      (equal x y)
      (equal y x)))))

(value-triple :itpeval-statement-checked)
:q
