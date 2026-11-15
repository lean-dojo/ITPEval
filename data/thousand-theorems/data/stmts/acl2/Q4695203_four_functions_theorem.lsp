;; Statement-only formalization of thousand-theorems corpus artifact Q4695203,
;; "Four functions theorem": the Ahlswede-Daykin inequality for four
;; nonnegative functions on an arbitrary distributive lattice, evaluated over
;; two finite subsets. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols represent the arbitrary lattice carrier,
;; coefficient carrier, operations, order, and four functions. Their laws are
;; explicit below and DEFUN-SK quantifiers are unbounded. Only the two source
;; Finset arguments are represented by duplicate-free finite lists.

(defstub q4695203-alpha-p (x) t)
(defstub q4695203-meet (x y) t)
(defstub q4695203-join (x y) t)

(defstub q4695203-beta-p (x) t)
(defstub q4695203-zero () t)
(defstub q4695203-one () t)
(defstub q4695203-add (x y) t)
(defstub q4695203-multiply (x y) t)
(defstub q4695203-less-equal (x y) t)

(defstub q4695203-f1 (x) t)
(defstub q4695203-f2 (x) t)
(defstub q4695203-f3 (x) t)
(defstub q4695203-f4 (x) t)

(defun q4695203-less (x y)
  (and
   (q4695203-less-equal x y)
   (not (equal x y))))

;; Equational distributive lattices are equivalent to ordered
;; DistribLattice structures, with x <= y defined by meet(x,y) = x.

(defun-sk q4695203-lattice-closure-p ()
  (forall (x y)
    (implies
     (and
      (q4695203-alpha-p x)
      (q4695203-alpha-p y))
     (and
      (q4695203-alpha-p (q4695203-meet x y))
      (q4695203-alpha-p (q4695203-join x y))))))

(defun-sk q4695203-lattice-laws-p ()
  (forall (x y z)
    (implies
     (and
      (q4695203-alpha-p x)
      (q4695203-alpha-p y)
      (q4695203-alpha-p z))
     (and
      (equal
       (q4695203-meet x y)
       (q4695203-meet y x))
      (equal
       (q4695203-join x y)
       (q4695203-join y x))
      (equal
       (q4695203-meet (q4695203-meet x y) z)
       (q4695203-meet x (q4695203-meet y z)))
      (equal
       (q4695203-join (q4695203-join x y) z)
       (q4695203-join x (q4695203-join y z)))
      (equal
       (q4695203-meet x (q4695203-join x y))
       x)
      (equal
       (q4695203-join x (q4695203-meet x y))
       x)
      (equal
       (q4695203-meet x (q4695203-join y z))
       (q4695203-join
        (q4695203-meet x y)
        (q4695203-meet x z)))
      (equal
       (q4695203-join x (q4695203-meet y z))
       (q4695203-meet
        (q4695203-join x y)
        (q4695203-join x z)))))))

(defun q4695203-distributive-lattice-p ()
  (and
   (q4695203-lattice-closure-p)
   (q4695203-lattice-laws-p)))

;; Exact first-order laws for CommSemiring, LinearOrder, and
;; IsStrictOrderedRing.

(defun-sk q4695203-coefficient-closure-p ()
  (forall (x y)
    (implies
     (and
      (q4695203-beta-p x)
      (q4695203-beta-p y))
     (and
      (q4695203-beta-p (q4695203-add x y))
      (q4695203-beta-p (q4695203-multiply x y))))))

(defun-sk q4695203-commutative-semiring-laws-p ()
  (forall (x y z)
    (implies
     (and
      (q4695203-beta-p x)
      (q4695203-beta-p y)
      (q4695203-beta-p z))
     (and
      (equal
       (q4695203-add (q4695203-add x y) z)
       (q4695203-add x (q4695203-add y z)))
      (equal
       (q4695203-add x y)
       (q4695203-add y x))
      (equal
       (q4695203-add x (q4695203-zero))
       x)
      (equal
       (q4695203-multiply (q4695203-multiply x y) z)
       (q4695203-multiply x (q4695203-multiply y z)))
      (equal
       (q4695203-multiply x y)
       (q4695203-multiply y x))
      (equal
       (q4695203-multiply x (q4695203-one))
       x)
      (equal
       (q4695203-multiply x (q4695203-add y z))
       (q4695203-add
        (q4695203-multiply x y)
        (q4695203-multiply x z)))
      (equal
       (q4695203-multiply x (q4695203-zero))
       (q4695203-zero))))))

(defun-sk q4695203-linear-order-laws-p ()
  (forall (x y z)
    (implies
     (and
      (q4695203-beta-p x)
      (q4695203-beta-p y)
      (q4695203-beta-p z))
     (and
      (q4695203-less-equal x x)
      (implies
       (and
        (q4695203-less-equal x y)
        (q4695203-less-equal y z))
       (q4695203-less-equal x z))
      (implies
       (and
        (q4695203-less-equal x y)
        (q4695203-less-equal y x))
       (equal x y))
      (or
       (q4695203-less-equal x y)
       (q4695203-less-equal y x))))))

(defun-sk q4695203-strict-ordered-ring-laws-p ()
  (forall (x y z)
    (implies
     (and
      (q4695203-beta-p x)
      (q4695203-beta-p y)
      (q4695203-beta-p z))
     (and
      ;; IsOrderedCancelAddMonoid.
      (implies
       (q4695203-less-equal y z)
       (q4695203-less-equal
        (q4695203-add x y)
        (q4695203-add x z)))
      (implies
       (q4695203-less-equal
        (q4695203-add x y)
        (q4695203-add x z))
       (q4695203-less-equal y z))
      ;; PosMulStrictMono and MulPosStrictMono.
      (implies
       (and
        (q4695203-less (q4695203-zero) x)
        (q4695203-less y z))
       (q4695203-less
        (q4695203-multiply x y)
        (q4695203-multiply x z)))
      (implies
       (and
        (q4695203-less (q4695203-zero) z)
        (q4695203-less x y))
       (q4695203-less
        (q4695203-multiply x z)
        (q4695203-multiply y z)))))))

;; The existential witness remains internal, exactly as in ExistsAddOfLE.

(defun-sk q4695203-add-complement-exists-p (x y)
  (exists (c)
    (and
     (q4695203-beta-p c)
     (equal y (q4695203-add x c)))))

(defun-sk q4695203-exists-add-of-le-p ()
  (forall (x y)
    (implies
     (and
      (q4695203-beta-p x)
      (q4695203-beta-p y)
      (q4695203-less-equal x y))
     (q4695203-add-complement-exists-p x y))))

(defun q4695203-coefficient-structure-p ()
  (and
   (q4695203-beta-p (q4695203-zero))
   (q4695203-beta-p (q4695203-one))
   (not (equal (q4695203-zero) (q4695203-one)))
   (q4695203-coefficient-closure-p)
   (q4695203-commutative-semiring-laws-p)
   (q4695203-linear-order-laws-p)
   (q4695203-less-equal
    (q4695203-zero) (q4695203-one))
   (q4695203-strict-ordered-ring-laws-p)
   (q4695203-exists-add-of-le-p)))

;; Typing and pointwise nonnegativity of the four arbitrary functions.

(defun-sk q4695203-function-laws-p ()
  (forall (x)
    (implies
     (q4695203-alpha-p x)
     (and
      (q4695203-beta-p (q4695203-f1 x))
      (q4695203-beta-p (q4695203-f2 x))
      (q4695203-beta-p (q4695203-f3 x))
      (q4695203-beta-p (q4695203-f4 x))
      (q4695203-less-equal
       (q4695203-zero) (q4695203-f1 x))
      (q4695203-less-equal
       (q4695203-zero) (q4695203-f2 x))
      (q4695203-less-equal
       (q4695203-zero) (q4695203-f3 x))
      (q4695203-less-equal
       (q4695203-zero) (q4695203-f4 x))))))

;; The pointwise four-functions hypothesis.

(defun-sk q4695203-modular-p ()
  (forall (x y)
    (implies
     (and
      (q4695203-alpha-p x)
      (q4695203-alpha-p y))
     (q4695203-less-equal
      (q4695203-multiply
       (q4695203-f1 x)
       (q4695203-f2 y))
      (q4695203-multiply
       (q4695203-f3 (q4695203-meet x y))
       (q4695203-f4 (q4695203-join x y)))))))

(defun q4695203-finite-subset-p (elements)
  (if (consp elements)
      (and
       (q4695203-alpha-p (car elements))
       (not (member-equal (car elements) (cdr elements)))
       (q4695203-finite-subset-p (cdr elements)))
    (equal elements nil)))

(defun q4695203-insert-set (object elements)
  (if (member-equal object elements)
      elements
    (cons object elements)))

(defun q4695203-infs-row (left right-elements accumulator)
  (if (consp right-elements)
      (q4695203-infs-row
       left
       (cdr right-elements)
       (q4695203-insert-set
        (q4695203-meet left (car right-elements))
        accumulator))
    accumulator))

(defun q4695203-infs (left-elements right-elements)
  (if (consp left-elements)
      (q4695203-infs-row
       (car left-elements)
       right-elements
       (q4695203-infs
        (cdr left-elements) right-elements))
    nil))

(defun q4695203-sups-row (left right-elements accumulator)
  (if (consp right-elements)
      (q4695203-sups-row
       left
       (cdr right-elements)
       (q4695203-insert-set
        (q4695203-join left (car right-elements))
        accumulator))
    accumulator))

(defun q4695203-sups (left-elements right-elements)
  (if (consp left-elements)
      (q4695203-sups-row
       (car left-elements)
       right-elements
       (q4695203-sups
        (cdr left-elements) right-elements))
    nil))

(defun q4695203-sum-f1 (elements)
  (if (consp elements)
      (q4695203-add
       (q4695203-f1 (car elements))
       (q4695203-sum-f1 (cdr elements)))
    (q4695203-zero)))

(defun q4695203-sum-f2 (elements)
  (if (consp elements)
      (q4695203-add
       (q4695203-f2 (car elements))
       (q4695203-sum-f2 (cdr elements)))
    (q4695203-zero)))

(defun q4695203-sum-f3 (elements)
  (if (consp elements)
      (q4695203-add
       (q4695203-f3 (car elements))
       (q4695203-sum-f3 (cdr elements)))
    (q4695203-zero)))

(defun q4695203-sum-f4 (elements)
  (if (consp elements)
      (q4695203-add
       (q4695203-f4 (car elements))
       (q4695203-sum-f4 (cdr elements)))
    (q4695203-zero)))

(defun thousand-theorems-q4695203-four-functions-theorem-statement
    (set-s set-t)
  (implies
   (and
    (q4695203-distributive-lattice-p)
    (q4695203-coefficient-structure-p)
    (q4695203-function-laws-p)
    (q4695203-modular-p)
    (q4695203-finite-subset-p set-s)
    (q4695203-finite-subset-p set-t))
   (q4695203-less-equal
    (q4695203-multiply
     (q4695203-sum-f1 set-s)
     (q4695203-sum-f2 set-t))
    (q4695203-multiply
     (q4695203-sum-f3
      (q4695203-infs set-s set-t))
     (q4695203-sum-f4
      (q4695203-sups set-s set-t))))))

(value-triple :itpeval-statement-checked)
:q
