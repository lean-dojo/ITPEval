;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/airborne/float_rmat_inv/float_rmat_inv_Why3_ide_VCfloat_rmat_inv_post_goal0:
;; nine sequential writes copy a real 3-by-3 matrix into separate writable
;; storage in transposed order under the stated memory conditions, yielding
;; the transpose relation. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars range over an arbitrary real closed ordered field. Real closed
;; fields have the same first-order theory as the mathematical reals, so this
;; preserves the source real domain without restricting it to ACL2 rationals.

(defstub rmi-real-op (ctx x) t)
(defstub rmi-add-op (ctx x y) t)
(defstub rmi-mul-op (ctx x y) t)
(defstub rmi-neg-op (ctx x) t)
(defstub rmi-inv-op (ctx x) t)
(defstub rmi-lt-op (ctx x y) t)

(defun rmi-real-p (ctx x)
  (if (rmi-real-op ctx x) t nil))

(defun rmi-add (ctx x y)
  (rmi-add-op ctx x y))

(defun rmi-mul (ctx x y)
  (rmi-mul-op ctx x y))

(defun rmi-neg (ctx x)
  (rmi-neg-op ctx x))

(defun rmi-inv (ctx x)
  (rmi-inv-op ctx x))

(defun rmi-lt (ctx x y)
  (if (rmi-lt-op ctx x y) t nil))

(defun rmi-le (ctx x y)
  (not (rmi-lt ctx y x)))

(defun-sk rmi-field-laws-p (ctx zero one)
  (forall (x y z)
    (implies
     (and
      (rmi-real-p ctx x)
      (rmi-real-p ctx y)
      (rmi-real-p ctx z))
     (and
      (rmi-real-p ctx (rmi-add ctx x y))
      (rmi-real-p ctx (rmi-mul ctx x y))
      (rmi-real-p ctx (rmi-neg ctx x))
      (rmi-real-p ctx (rmi-inv ctx x))
      (equal
       (rmi-add ctx (rmi-add ctx x y) z)
       (rmi-add ctx x (rmi-add ctx y z)))
      (equal (rmi-add ctx x y) (rmi-add ctx y x))
      (equal (rmi-add ctx x zero) x)
      (equal (rmi-add ctx x (rmi-neg ctx x)) zero)
      (equal
       (rmi-mul ctx (rmi-mul ctx x y) z)
       (rmi-mul ctx x (rmi-mul ctx y z)))
      (equal (rmi-mul ctx x y) (rmi-mul ctx y x))
      (equal (rmi-mul ctx x one) x)
      (equal (rmi-inv ctx zero) zero)
      (implies
       (not (equal x zero))
       (equal (rmi-mul ctx x (rmi-inv ctx x)) one))
      (equal
       (rmi-mul ctx x (rmi-add ctx y z))
       (rmi-add
        ctx
        (rmi-mul ctx x y)
        (rmi-mul ctx x z)))))))

(defun-sk rmi-order-laws-p (ctx zero)
  (forall (x y z)
    (implies
     (and
      (rmi-real-p ctx x)
      (rmi-real-p ctx y)
      (rmi-real-p ctx z))
     (and
      (not (rmi-lt ctx x x))
      (or
       (equal x y)
       (rmi-lt ctx x y)
       (rmi-lt ctx y x))
      (implies
       (and (rmi-lt ctx x y) (rmi-lt ctx y z))
       (rmi-lt ctx x z))
      (implies
       (rmi-lt ctx x y)
       (rmi-lt
        ctx
        (rmi-add ctx x z)
        (rmi-add ctx y z)))
      (implies
       (and (rmi-lt ctx zero x) (rmi-lt ctx zero y))
       (rmi-lt ctx zero (rmi-mul ctx x y)))))))

(defun-sk rmi-positive-square-root-exists-p (ctx zero x)
  (exists (root)
    (and
     (rmi-real-p ctx root)
     (rmi-le ctx zero root)
     (equal (rmi-mul ctx root root) x))))

(defun-sk rmi-positive-square-root-laws-p (ctx zero)
  (forall (x)
    (implies
     (and
      (rmi-real-p ctx x)
      (rmi-lt ctx zero x))
     (rmi-positive-square-root-exists-p ctx zero x))))

(defun rmi-real-coefficient-list-p (ctx coefficients)
  (if (consp coefficients)
      (and
       (rmi-real-p ctx (car coefficients))
       (rmi-real-coefficient-list-p ctx (cdr coefficients)))
    (equal coefficients nil)))

(defun rmi-poly-eval (ctx zero coefficients x)
  (if (consp coefficients)
      (rmi-add
       ctx
       (car coefficients)
       (rmi-mul
        ctx
        x
        (rmi-poly-eval ctx zero (cdr coefficients) x)))
    zero))

(defun-sk rmi-odd-polynomial-root-exists-p
    (ctx zero coefficients)
  (exists (root)
    (and
     (rmi-real-p ctx root)
     (equal
      (rmi-poly-eval ctx zero coefficients root)
      zero))))

(defun-sk rmi-odd-root-laws-p (ctx zero)
  (forall (coefficients degree)
    (implies
     (and
      (natp degree)
      (not (equal degree 0))
      (oddp degree)
      (true-listp coefficients)
      (consp coefficients)
      (equal (len coefficients) (+ 1 degree))
      (rmi-real-coefficient-list-p ctx coefficients)
      (not (equal (car (last coefficients)) zero)))
     (rmi-odd-polynomial-root-exists-p
      ctx zero coefficients))))

(defun rmi-real-context-p (ctx zero one)
  (and
   (rmi-real-p ctx zero)
   (rmi-real-p ctx one)
   (not (equal zero one))
   (rmi-lt ctx zero one)
   (rmi-field-laws-p ctx zero one)
   (rmi-order-laws-p ctx zero)
   (rmi-positive-square-root-laws-p ctx zero)
   (rmi-odd-root-laws-p ctx zero)))

;; Addresses are exactly pairs of mathematical integers, matching the source
;; address record with integer base and offset fields.

(defun rmi-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun rmi-address-base (address)
  (car address))

(defun rmi-address-offset (address)
  (cdr address))

(defun rmi-shift (address amount)
  (cons
   (rmi-address-base address)
   (+ (rmi-address-offset address) amount)))

;; Tagged conservative interfaces preserve the arbitrary source functions
;; t_1 : address -> real and t : integer -> integer, together with the fixed
;; arbitrary region function and linked predicate.

(defstub rmi-memory-at (memory-tag address) t)
(defstub rmi-malloc-at (malloc-tag index) t)
(defstub rmi-region-op (base) t)
(defstub rmi-linked-op (malloc-tag) t)

(defun-sk rmi-memory-function-p (ctx memory-tag)
  (forall (address)
    (implies
     (rmi-address-p address)
     (rmi-real-p ctx (rmi-memory-at memory-tag address)))))

(defun-sk rmi-malloc-function-p (malloc-tag)
  (forall (index)
    (implies
     (integerp index)
     (integerp (rmi-malloc-at malloc-tag index)))))

(defun-sk rmi-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (rmi-region-op base)))))

(defun rmi-linked-p (malloc-tag)
  (if (rmi-linked-op malloc-tag) t nil))

(defun rmi-valid-rw-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (< 0 (rmi-address-base address))
    (<= 0 (rmi-address-offset address))
    (<=
     (+ (rmi-address-offset address) length)
     (rmi-malloc-at
      malloc-tag
      (rmi-address-base address))))))

(defun rmi-valid-rd-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (rmi-address-base address)))
    (<= 0 (rmi-address-offset address))
    (<=
     (+ (rmi-address-offset address) length)
     (rmi-malloc-at
      malloc-tag
      (rmi-address-base address))))))

(defun rmi-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (rmi-address-base left)
     (rmi-address-base right)))
   (<=
    (+ (rmi-address-offset right) right-length)
    (rmi-address-offset left))
   (<=
    (+ (rmi-address-offset left) left-length)
    (rmi-address-offset right))))

;; An update list is newest first. Assoc-equal therefore implements the exact
;; successive Function.update semantics, including all possible aliasing.

(defun rmi-memory-read (memory-tag updates address)
  (let ((entry (assoc-equal address updates)))
    (if entry
        (cdr entry)
      (rmi-memory-at memory-tag address))))

(defun rmi-memory-write (updates address value)
  (cons (cons address value) updates))

;; The imported source theory proves is_finite32 for every real, so its
;; occurrences in the matrix-validity predicate are definitionally true here.

(defun rmi-is-finite32-p (value)
  (declare (ignore value))
  t)

(defun rmi-finite-floatrmat-p
    (memory-tag updates address)
  (let ((base (rmi-shift address 0)))
    (and
     (rmi-is-finite32-p
      (rmi-memory-read memory-tag updates (rmi-shift base 0)))
     (rmi-is-finite32-p
      (rmi-memory-read memory-tag updates (rmi-shift base 1)))
     (rmi-is-finite32-p
      (rmi-memory-read memory-tag updates (rmi-shift base 2)))
     (rmi-is-finite32-p
      (rmi-memory-read memory-tag updates (rmi-shift base 3)))
     (rmi-is-finite32-p
      (rmi-memory-read memory-tag updates (rmi-shift base 4)))
     (rmi-is-finite32-p
      (rmi-memory-read memory-tag updates (rmi-shift base 5)))
     (rmi-is-finite32-p
      (rmi-memory-read memory-tag updates (rmi-shift base 6)))
     (rmi-is-finite32-p
      (rmi-memory-read memory-tag updates (rmi-shift base 7)))
     (rmi-is-finite32-p
      (rmi-memory-read memory-tag updates (rmi-shift base 8))))))

(defun rmi-rvalid-floatrmat-p
    (malloc-tag memory-tag updates address)
  (and
   (rmi-finite-floatrmat-p memory-tag updates address)
   (rmi-valid-rd-p malloc-tag address 9)))

;; Matrices are row-major nine-tuples, exactly matching the nine-field source
;; record. The equality predicate unfolds the source record equality.

(defun rmi-matrix
    (a00 a01 a02 a10 a11 a12 a20 a21 a22)
  (list a00 a01 a02 a10 a11 a12 a20 a21 a22))

(defun rmi-matrix-entry (matrix row column)
  (nth (+ (* 3 row) column) matrix))

(defun rmi-matrix-of-memory (memory-tag updates address)
  (let ((base (rmi-shift address 0)))
    (rmi-matrix
     (rmi-memory-read memory-tag updates (rmi-shift base 0))
     (rmi-memory-read memory-tag updates (rmi-shift base 1))
     (rmi-memory-read memory-tag updates (rmi-shift base 2))
     (rmi-memory-read memory-tag updates (rmi-shift base 3))
     (rmi-memory-read memory-tag updates (rmi-shift base 4))
     (rmi-memory-read memory-tag updates (rmi-shift base 5))
     (rmi-memory-read memory-tag updates (rmi-shift base 6))
     (rmi-memory-read memory-tag updates (rmi-shift base 7))
     (rmi-memory-read memory-tag updates (rmi-shift base 8)))))

(defun rmi-matrix-transpose (matrix)
  (rmi-matrix
   (rmi-matrix-entry matrix 0 0)
   (rmi-matrix-entry matrix 1 0)
   (rmi-matrix-entry matrix 2 0)
   (rmi-matrix-entry matrix 0 1)
   (rmi-matrix-entry matrix 1 1)
   (rmi-matrix-entry matrix 2 1)
   (rmi-matrix-entry matrix 0 2)
   (rmi-matrix-entry matrix 1 2)
   (rmi-matrix-entry matrix 2 2)))

(defun rmi-matrix-equal-p (left right)
  (and
   (equal
    (rmi-matrix-entry left 0 0)
    (rmi-matrix-entry right 0 0))
   (equal
    (rmi-matrix-entry left 0 1)
    (rmi-matrix-entry right 0 1))
   (equal
    (rmi-matrix-entry left 0 2)
    (rmi-matrix-entry right 0 2))
   (equal
    (rmi-matrix-entry left 1 0)
    (rmi-matrix-entry right 1 0))
   (equal
    (rmi-matrix-entry left 1 1)
    (rmi-matrix-entry right 1 1))
   (equal
    (rmi-matrix-entry left 1 2)
    (rmi-matrix-entry right 1 2))
   (equal
    (rmi-matrix-entry left 2 0)
    (rmi-matrix-entry right 2 0))
   (equal
    (rmi-matrix-entry left 2 1)
    (rmi-matrix-entry right 2 1))
   (equal
    (rmi-matrix-entry left 2 2)
    (rmi-matrix-entry right 2 2))))

(defun-sk
    ntp4vc-float-rmat-inv-post-goal0-statement ()
  (forall
   (ctx zero one a a-1 memory-tag malloc-tag)
   (implies
    (and
     (rmi-real-context-p ctx zero one)
     (rmi-address-p a)
     (rmi-address-p a-1)
     (rmi-memory-function-p ctx memory-tag)
     (rmi-malloc-function-p malloc-tag)
     (rmi-region-function-p))
    (let*
        ((a-2 (rmi-shift a 0))
         (a-3 (rmi-shift a-1 0))
         (updates-0 nil)
         (updates-1
          (rmi-memory-write
           updates-0
           (rmi-shift a-2 0)
           (rmi-memory-read
            memory-tag updates-0 (rmi-shift a-3 0))))
         (updates-2
          (rmi-memory-write
           updates-1
           (rmi-shift a-2 1)
           (rmi-memory-read
            memory-tag updates-1 (rmi-shift a-3 3))))
         (updates-3
          (rmi-memory-write
           updates-2
           (rmi-shift a-2 2)
           (rmi-memory-read
            memory-tag updates-2 (rmi-shift a-3 6))))
         (updates-4
          (rmi-memory-write
           updates-3
           (rmi-shift a-2 3)
           (rmi-memory-read
            memory-tag updates-3 (rmi-shift a-3 1))))
         (updates-5
          (rmi-memory-write
           updates-4
           (rmi-shift a-2 4)
           (rmi-memory-read
            memory-tag updates-4 (rmi-shift a-3 4))))
         (updates-6
          (rmi-memory-write
           updates-5
           (rmi-shift a-2 5)
           (rmi-memory-read
            memory-tag updates-5 (rmi-shift a-3 7))))
         (updates-7
          (rmi-memory-write
           updates-6
           (rmi-shift a-2 6)
           (rmi-memory-read
            memory-tag updates-6 (rmi-shift a-3 2))))
         (updates-8
          (rmi-memory-write
           updates-7
           (rmi-shift a-2 7)
           (rmi-memory-read
            memory-tag updates-7 (rmi-shift a-3 5))))
         (updates-9
          (rmi-memory-write
           updates-8
           (rmi-shift a-2 8)
           (rmi-memory-read
            memory-tag updates-8 (rmi-shift a-3 8)))))
      (implies
       (and
        (<= (rmi-region-op (rmi-address-base a)) 0)
        (<= (rmi-region-op (rmi-address-base a-1)) 0)
        (rmi-linked-p malloc-tag)
        (rmi-valid-rw-p malloc-tag a 9)
        (rmi-rvalid-floatrmat-p
         malloc-tag memory-tag updates-0 a-1)
        (rmi-separated-p a 9 a-1 9))
       (rmi-matrix-equal-p
        (rmi-matrix-transpose
         (rmi-matrix-of-memory memory-tag updates-9 a-1))
        (rmi-matrix-of-memory
         memory-tag updates-9 a)))))))

(value-triple :itpeval-statement-checked)

:q
