;; Statement-only formalization of Logipedia corpus artifact
;; nat.sym_eq_match_nat_type_S, catalog title "nat.sym_eq_match_nat_type_S":
;; for every result type, zero case, successor branch, and natural n, the
;; natural-number eliminator at S n equals the branch value at n. This file
;; contains no proof.

(in-package "ACL2")

;; RETURN-TYPE and CASE-S remain arbitrary ACL2 objects. These conservative
;; interfaces interpret the former as a carrier and the latter as a function.
(defstub logipedia-nat-sym-eq-match-s-member-p
  (return-type value) t)

(defstub logipedia-nat-sym-eq-match-s-function-at
  (function argument) t)

(defun-sk logipedia-nat-sym-eq-match-s-function-values-p
    (return-type function)
  (forall (argument)
    (implies
     (natp argument)
     (logipedia-nat-sym-eq-match-s-member-p
      return-type
      (logipedia-nat-sym-eq-match-s-function-at
       function argument)))))

;; ACL2 naturals give the definitional presentation O = 0 and S n = n + 1.
(defun logipedia-nat-sym-eq-match-s-match
    (case-o case-s n)
  (if (zp n)
      case-o
    (logipedia-nat-sym-eq-match-s-function-at
     case-s (- n 1))))

(defun logipedia-nat-sym-eq-match-s-statement
    (return-type case-o case-s n)
  (implies
   (and
    (logipedia-nat-sym-eq-match-s-member-p
     return-type case-o)
    (logipedia-nat-sym-eq-match-s-function-values-p
     return-type case-s)
    (natp n))
   (equal
    (logipedia-nat-sym-eq-match-s-function-at case-s n)
    (logipedia-nat-sym-eq-match-s-match
     case-o case-s (+ n 1)))))

(value-triple :itpeval-statement-checked)
:q
