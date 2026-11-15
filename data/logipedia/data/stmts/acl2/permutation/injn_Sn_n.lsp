;; Statement-only formalization of Logipedia corpus artifact
;; permutation.injn_Sn_n, catalog title "permutation.injn_Sn_n": injectivity
;; of an arbitrary natural-valued function on zero through n+1 implies
;; injectivity on zero through n. This file contains no proof.

(in-package "ACL2")

(defstub logipedia-permutation-injn-sn-n-f (index) t)

(defun-sk logipedia-permutation-injn-sn-n-natural-function-p ()
  (forall (index)
    (implies (natp index)
             (natp (logipedia-permutation-injn-sn-n-f index)))))

(defun-sk logipedia-permutation-injn-sn-n-injn-p (n)
  (forall (left right)
    (implies
      (and (natp left)
           (natp right)
           (<= left n)
           (<= right n)
           (equal (logipedia-permutation-injn-sn-n-f left)
                  (logipedia-permutation-injn-sn-n-f right)))
      (equal left right))))

(defun-sk logipedia-permutation-injn-sn-n-statement ()
  (forall (n)
    (implies
      (and (natp n)
           (logipedia-permutation-injn-sn-n-natural-function-p)
           (logipedia-permutation-injn-sn-n-injn-p (+ 1 n)))
      (logipedia-permutation-injn-sn-n-injn-p n))))

(value-triple :itpeval-statement-checked)
:q
