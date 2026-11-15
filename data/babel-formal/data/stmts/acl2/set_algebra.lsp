;; Statement-only formalization of Babel-formal artifact set_algebra: the two
;; pointwise distributive laws for set intersection and union, and both De
;; Morgan laws for set complement, encoded by arbitrary Boolean membership
;; values. This file contains no proof.

(in-package "ACL2")

(defun set-algebra-union-at (a-at-x b-at-x)
  (or a-at-x b-at-x))

(defun set-algebra-intersection-at (a-at-x b-at-x)
  (and a-at-x b-at-x))

(defun set-algebra-complement-at (a-at-x)
  (not a-at-x))

(defun set-algebra-inter-distrib-left-statement
    (a-at-x b-at-x c-at-x)
  (implies
   (and (booleanp a-at-x)
        (booleanp b-at-x)
        (booleanp c-at-x))
   (equal
    (set-algebra-intersection-at
     a-at-x
     (set-algebra-union-at b-at-x c-at-x))
    (set-algebra-union-at
     (set-algebra-intersection-at a-at-x b-at-x)
     (set-algebra-intersection-at a-at-x c-at-x)))))

(defun set-algebra-inter-distrib-right-statement
    (a-at-x b-at-x c-at-x)
  (implies
   (and (booleanp a-at-x)
        (booleanp b-at-x)
        (booleanp c-at-x))
   (equal
    (set-algebra-intersection-at
     (set-algebra-union-at a-at-x b-at-x)
     c-at-x)
    (set-algebra-union-at
     (set-algebra-intersection-at a-at-x c-at-x)
     (set-algebra-intersection-at b-at-x c-at-x)))))

(defun set-algebra-de-morgan-union-statement (a-at-x b-at-x)
  (implies
   (and (booleanp a-at-x)
        (booleanp b-at-x))
   (equal
    (set-algebra-complement-at
     (set-algebra-union-at a-at-x b-at-x))
    (set-algebra-intersection-at
     (set-algebra-complement-at a-at-x)
     (set-algebra-complement-at b-at-x)))))

(defun set-algebra-de-morgan-intersection-statement
    (a-at-x b-at-x)
  (implies
   (and (booleanp a-at-x)
        (booleanp b-at-x))
   (equal
    (set-algebra-complement-at
     (set-algebra-intersection-at a-at-x b-at-x))
    (set-algebra-union-at
     (set-algebra-complement-at a-at-x)
     (set-algebra-complement-at b-at-x)))))

(value-triple :itpeval-statement-checked)
:q
