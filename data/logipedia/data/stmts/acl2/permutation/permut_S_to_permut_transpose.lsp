;; Statement-only formalization of Logipedia corpus artifact
;; permutation.permut_S_to_permut_transpose, catalog title
;; "permutation.permut_S_to_permut_transpose": transposing the final value of
;; a natural-number permutation on zero through m+1 yields a permutation on
;; zero through m. This file contains no proof.

(in-package "ACL2")

(defstub logipedia-permutation-permut-s-to-transpose-f (index) t)

(defun-sk logipedia-permutation-permut-s-to-transpose-natural-function-p ()
  (forall (index)
    (implies
     (natp index)
     (natp
      (logipedia-permutation-permut-s-to-transpose-f index)))))

(defun logipedia-permutation-permut-s-to-transpose (i j natural)
  (if (equal natural i)
      j
    (if (equal natural j)
        i
      natural)))

(defun-sk logipedia-permutation-permut-s-to-transpose-range-p (n)
  (forall (index)
    (implies
     (and
      (natp index)
      (<= index n))
     (and
      (natp
       (logipedia-permutation-permut-s-to-transpose-f index))
      (<=
       (logipedia-permutation-permut-s-to-transpose-f index)
       n)))))

(defun-sk logipedia-permutation-permut-s-to-transpose-injective-p (n)
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right)
      (<= left n)
      (<= right n)
      (equal
       (logipedia-permutation-permut-s-to-transpose-f left)
       (logipedia-permutation-permut-s-to-transpose-f right)))
     (equal left right))))

(defun logipedia-permutation-permut-s-to-transpose-permut-p (n)
  (and
   (logipedia-permutation-permut-s-to-transpose-range-p n)
   (logipedia-permutation-permut-s-to-transpose-injective-p n)))

(defun logipedia-permutation-permut-s-to-transpose-transformed
    (m index)
  (logipedia-permutation-permut-s-to-transpose
   (logipedia-permutation-permut-s-to-transpose-f (+ 1 m))
   (+ 1 m)
   (logipedia-permutation-permut-s-to-transpose-f index)))

(defun-sk
    logipedia-permutation-permut-s-to-transpose-transformed-range-p
    (m)
  (forall (index)
    (implies
     (and
      (natp index)
      (<= index m))
     (and
      (natp
       (logipedia-permutation-permut-s-to-transpose-transformed
        m index))
      (<=
       (logipedia-permutation-permut-s-to-transpose-transformed
        m index)
       m)))))

(defun-sk
    logipedia-permutation-permut-s-to-transpose-transformed-injective-p
    (m)
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right)
      (<= left m)
      (<= right m)
      (equal
       (logipedia-permutation-permut-s-to-transpose-transformed
        m left)
       (logipedia-permutation-permut-s-to-transpose-transformed
        m right)))
     (equal left right))))

(defun logipedia-permutation-permut-s-to-transpose-transformed-permut-p
    (m)
  (and
   (logipedia-permutation-permut-s-to-transpose-transformed-range-p
    m)
   (logipedia-permutation-permut-s-to-transpose-transformed-injective-p
    m)))

(defun-sk logipedia-permutation-permut-s-to-transpose-statement ()
  (forall (m)
    (implies
     (and
      (natp m)
      (logipedia-permutation-permut-s-to-transpose-natural-function-p)
      (logipedia-permutation-permut-s-to-transpose-permut-p
       (+ 1 m)))
     (logipedia-permutation-permut-s-to-transpose-transformed-permut-p
      m))))

(value-triple :itpeval-statement-checked)
:q
