;; Statement-only formalization of Logipedia corpus artifact
;; permutation.let_clause_1068, catalog title "permutation.let_clause_1068":
;; for a permutation of the naturals through n, the stated bounded preimage,
;; range, injectivity, and equality assumptions imply that the first
;; preimage maps to its specified value. This file contains no proof.

(in-package "ACL2")

(defstub logipedia-permutation-let-clause-1068-f (index) t)

(defun-sk logipedia-permutation-let-clause-1068-natural-function-p ()
  (forall (index)
    (implies
     (natp index)
     (natp
      (logipedia-permutation-let-clause-1068-f index)))))

(defun-sk logipedia-permutation-let-clause-1068-maps-interval-p (n)
  (forall (index)
    (implies
     (and
      (natp index)
      (<= index n))
     (<= (logipedia-permutation-let-clause-1068-f index)
         n))))

(defun-sk logipedia-permutation-let-clause-1068-injn-p (n)
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right)
      (<= left n)
      (<= right n)
      (equal
       (logipedia-permutation-let-clause-1068-f left)
       (logipedia-permutation-let-clause-1068-f right)))
     (equal left right))))

(defun logipedia-permutation-let-clause-1068-permut-p (n)
  (and
   (logipedia-permutation-let-clause-1068-maps-interval-p n)
   (logipedia-permutation-let-clause-1068-injn-p n)))

(defun-sk logipedia-permutation-let-clause-1068-statement ()
  (forall (n i j a b)
    (implies
     (and
      (logipedia-permutation-let-clause-1068-natural-function-p)
      (natp n)
      (natp i)
      (natp j)
      (natp a)
      (natp b))
     (implies
      (logipedia-permutation-let-clause-1068-permut-p n)
      (implies
       (<= i n)
       (implies
        (<= j n)
        (implies
         (and
          (<= a n)
          (equal
           (logipedia-permutation-let-clause-1068-f a)
           i))
         (implies
          (<= a n)
          (implies
           (equal
            (logipedia-permutation-let-clause-1068-f a)
            i)
           (implies
            (and
             (<= b n)
             (equal
              (logipedia-permutation-let-clause-1068-f b)
              j))
            (implies
             (<= b n)
             (implies
              (equal
               (logipedia-permutation-let-clause-1068-f b)
               j)
              (implies
               (logipedia-permutation-let-clause-1068-maps-interval-p
                n)
               (implies
                (logipedia-permutation-let-clause-1068-injn-p n)
                (implies
                 (equal a b)
                 (equal
                  (logipedia-permutation-let-clause-1068-f a)
                  i))))))))))))))))

(value-triple :itpeval-statement-checked)
:q
