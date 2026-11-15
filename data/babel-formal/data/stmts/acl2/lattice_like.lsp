;; Statement-only formalization of Babel-formal artifact lattice_like: on an
;; arbitrary carrier, a partial order with infimum and supremum operations
;; satisfying their universal properties has commutative and associative meet
;; and join and satisfies both absorption laws. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the source's arbitrary type,
;; relation, and binary operations directly, without finite enumerations or
;; lookup tables. Every typing and lattice-like law is explicit below.

(defstub lattice-like-element-p (x) t)
(defstub lattice-like-le (x y) t)
(defstub lattice-like-inf (x y) t)
(defstub lattice-like-sup (x y) t)

(defun-sk lattice-like-operation-closure-p ()
  (forall (a b)
    (implies
     (and
      (lattice-like-element-p a)
      (lattice-like-element-p b))
     (and
      (lattice-like-element-p (lattice-like-inf a b))
      (lattice-like-element-p (lattice-like-sup a b))))))

(defun-sk lattice-like-le-reflexive-p ()
  (forall (x)
    (implies
     (lattice-like-element-p x)
     (lattice-like-le x x))))

(defun-sk lattice-like-le-transitive-p ()
  (forall (x y z)
    (implies
     (and
      (lattice-like-element-p x)
      (lattice-like-element-p y)
      (lattice-like-element-p z)
      (lattice-like-le x y)
      (lattice-like-le y z))
     (lattice-like-le x z))))

(defun-sk lattice-like-le-antisymmetric-p ()
  (forall (x y)
    (implies
     (and
      (lattice-like-element-p x)
      (lattice-like-element-p y)
      (lattice-like-le x y)
      (lattice-like-le y x))
     (equal x y))))

(defun-sk lattice-like-inf-lower-bounds-p ()
  (forall (a b)
    (implies
     (and
      (lattice-like-element-p a)
      (lattice-like-element-p b))
     (and
      (lattice-like-le (lattice-like-inf a b) a)
      (lattice-like-le (lattice-like-inf a b) b)))))

(defun-sk lattice-like-inf-greatest-p ()
  (forall (c a b)
    (implies
     (and
      (lattice-like-element-p c)
      (lattice-like-element-p a)
      (lattice-like-element-p b)
      (lattice-like-le c a)
      (lattice-like-le c b))
     (lattice-like-le c (lattice-like-inf a b)))))

(defun-sk lattice-like-sup-upper-bounds-p ()
  (forall (a b)
    (implies
     (and
      (lattice-like-element-p a)
      (lattice-like-element-p b))
     (and
      (lattice-like-le a (lattice-like-sup a b))
      (lattice-like-le b (lattice-like-sup a b))))))

(defun-sk lattice-like-sup-least-p ()
  (forall (a b c)
    (implies
     (and
      (lattice-like-element-p a)
      (lattice-like-element-p b)
      (lattice-like-element-p c)
      (lattice-like-le a c)
      (lattice-like-le b c))
     (lattice-like-le (lattice-like-sup a b) c))))

(defun lattice-like-structure-p ()
  (and
   (lattice-like-operation-closure-p)
   (lattice-like-le-reflexive-p)
   (lattice-like-le-transitive-p)
   (lattice-like-le-antisymmetric-p)
   (lattice-like-inf-lower-bounds-p)
   (lattice-like-inf-greatest-p)
   (lattice-like-sup-upper-bounds-p)
   (lattice-like-sup-least-p)))

(defun-sk lattice-like-inf-commutative-p ()
  (forall (a b)
    (implies
     (and
      (lattice-like-element-p a)
      (lattice-like-element-p b))
     (equal
      (lattice-like-inf a b)
      (lattice-like-inf b a)))))

(defun-sk lattice-like-sup-commutative-p ()
  (forall (a b)
    (implies
     (and
      (lattice-like-element-p a)
      (lattice-like-element-p b))
     (equal
      (lattice-like-sup a b)
      (lattice-like-sup b a)))))

(defun-sk lattice-like-inf-associative-p ()
  (forall (a b c)
    (implies
     (and
      (lattice-like-element-p a)
      (lattice-like-element-p b)
      (lattice-like-element-p c))
     (equal
      (lattice-like-inf (lattice-like-inf a b) c)
      (lattice-like-inf a (lattice-like-inf b c))))))

(defun-sk lattice-like-sup-associative-p ()
  (forall (a b c)
    (implies
     (and
      (lattice-like-element-p a)
      (lattice-like-element-p b)
      (lattice-like-element-p c))
     (equal
      (lattice-like-sup (lattice-like-sup a b) c)
      (lattice-like-sup a (lattice-like-sup b c))))))

(defun-sk lattice-like-inf-absorption-p ()
  (forall (a b)
    (implies
     (and
      (lattice-like-element-p a)
      (lattice-like-element-p b))
     (equal
      (lattice-like-inf a (lattice-like-sup a b))
      a))))

(defun-sk lattice-like-sup-absorption-p ()
  (forall (a b)
    (implies
     (and
      (lattice-like-element-p a)
      (lattice-like-element-p b))
     (equal
      (lattice-like-sup a (lattice-like-inf a b))
      a))))

(defun lattice-like-laws-p ()
  (and
   (lattice-like-inf-commutative-p)
   (lattice-like-sup-commutative-p)
   (lattice-like-inf-associative-p)
   (lattice-like-sup-associative-p)
   (lattice-like-inf-absorption-p)
   (lattice-like-sup-absorption-p)))

(defun lattice-like-statement ()
  (implies
   (lattice-like-structure-p)
   (lattice-like-laws-p)))

(value-triple :itpeval-statement-checked)
:q
