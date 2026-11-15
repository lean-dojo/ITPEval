;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/airborne/float_rmat_of_quat/float_rmat_of_quat_Why3_ide_VCfloat_rmat_of_quat_post_goal0:
;; the transpose of the nine real entries written from a unit quaternion
;; equals the real matrix defined directly from that quaternion under the
;; stated memory, validity, separation, and floating-value hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars range over an arbitrary real closed ordered field. Real closed
;; fields have the same first-order ordered-field theory as the mathematical
;; reals, so this does not restrict source reals to ACL2 rationals.

(defstub frq-real-op (ctx x) t)
(defstub frq-add-op (ctx x y) t)
(defstub frq-mul-op (ctx x y) t)
(defstub frq-neg-op (ctx x) t)
(defstub frq-inv-op (ctx x) t)
(defstub frq-lt-op (ctx x y) t)

(defun frq-real-p (ctx x)
  (if (frq-real-op ctx x) t nil))

(defun frq-add (ctx x y)
  (frq-add-op ctx x y))

(defun frq-mul (ctx x y)
  (frq-mul-op ctx x y))

(defun frq-neg (ctx x)
  (frq-neg-op ctx x))

(defun frq-inv (ctx x)
  (frq-inv-op ctx x))

(defun frq-lt (ctx x y)
  (if (frq-lt-op ctx x y) t nil))

(defun frq-le (ctx x y)
  (not (frq-lt ctx y x)))

(defun-sk frq-field-laws-p (ctx zero one)
  (forall (x y z)
    (implies
     (and
      (frq-real-p ctx x)
      (frq-real-p ctx y)
      (frq-real-p ctx z))
     (and
      (frq-real-p ctx (frq-add ctx x y))
      (frq-real-p ctx (frq-mul ctx x y))
      (frq-real-p ctx (frq-neg ctx x))
      (frq-real-p ctx (frq-inv ctx x))
      (equal
       (frq-add ctx (frq-add ctx x y) z)
       (frq-add ctx x (frq-add ctx y z)))
      (equal (frq-add ctx x y) (frq-add ctx y x))
      (equal (frq-add ctx x zero) x)
      (equal (frq-add ctx x (frq-neg ctx x)) zero)
      (equal
       (frq-mul ctx (frq-mul ctx x y) z)
       (frq-mul ctx x (frq-mul ctx y z)))
      (equal (frq-mul ctx x y) (frq-mul ctx y x))
      (equal (frq-mul ctx x one) x)
      (equal (frq-inv ctx zero) zero)
      (implies
       (not (equal x zero))
       (equal (frq-mul ctx x (frq-inv ctx x)) one))
      (equal
       (frq-mul ctx x (frq-add ctx y z))
       (frq-add
        ctx
        (frq-mul ctx x y)
        (frq-mul ctx x z)))))))

(defun-sk frq-order-laws-p (ctx zero)
  (forall (x y z)
    (implies
     (and
      (frq-real-p ctx x)
      (frq-real-p ctx y)
      (frq-real-p ctx z))
     (and
      (not (frq-lt ctx x x))
      (or
       (equal x y)
       (frq-lt ctx x y)
       (frq-lt ctx y x))
      (implies
       (and (frq-lt ctx x y) (frq-lt ctx y z))
       (frq-lt ctx x z))
      (implies
       (frq-lt ctx x y)
       (frq-lt
        ctx
        (frq-add ctx x z)
        (frq-add ctx y z)))
      (implies
       (and (frq-lt ctx zero x) (frq-lt ctx zero y))
       (frq-lt ctx zero (frq-mul ctx x y)))))))

(defun-sk frq-positive-square-root-exists-p (ctx zero x)
  (exists (root)
    (and
     (frq-real-p ctx root)
     (frq-le ctx zero root)
     (equal (frq-mul ctx root root) x))))

(defun-sk frq-positive-square-root-laws-p (ctx zero)
  (forall (x)
    (implies
     (and
      (frq-real-p ctx x)
      (frq-lt ctx zero x))
     (frq-positive-square-root-exists-p ctx zero x))))

(defun frq-real-coefficient-list-p (ctx coefficients)
  (if (consp coefficients)
      (and
       (frq-real-p ctx (car coefficients))
       (frq-real-coefficient-list-p ctx (cdr coefficients)))
    (equal coefficients nil)))

(defun frq-poly-eval (ctx zero coefficients x)
  (if (consp coefficients)
      (frq-add
       ctx
       (car coefficients)
       (frq-mul
        ctx
        x
        (frq-poly-eval ctx zero (cdr coefficients) x)))
    zero))

(defun-sk frq-odd-polynomial-root-exists-p
    (ctx zero coefficients)
  (exists (root)
    (and
     (frq-real-p ctx root)
     (equal
      (frq-poly-eval ctx zero coefficients root)
      zero))))

(defun-sk frq-odd-root-laws-p (ctx zero)
  (forall (coefficients degree)
    (implies
     (and
      (natp degree)
      (not (equal degree 0))
      (oddp degree)
      (true-listp coefficients)
      (consp coefficients)
      (equal (len coefficients) (+ 1 degree))
      (frq-real-coefficient-list-p ctx coefficients)
      (not (equal (car (last coefficients)) zero)))
     (frq-odd-polynomial-root-exists-p
      ctx zero coefficients))))

(defun frq-real-context-p (ctx zero one)
  (and
   (frq-real-p ctx zero)
   (frq-real-p ctx one)
   (not (equal zero one))
   (frq-lt ctx zero one)
   (frq-field-laws-p ctx zero one)
   (frq-order-laws-p ctx zero)
   (frq-positive-square-root-laws-p ctx zero)
   (frq-odd-root-laws-p ctx zero)))

(defun frq-two (ctx one)
  (frq-add ctx one one))

;; Addresses are exactly pairs of mathematical integers, matching the source
;; record with integer base and offset fields.

(defun frq-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun frq-address-base (address)
  (car address))

(defun frq-address-offset (address)
  (cdr address))

(defun frq-shift (address amount)
  (cons
   (frq-address-base address)
   (+ (frq-address-offset address) amount)))

;; Tagged conservative interfaces preserve the arbitrary source functions
;; t_1 : address -> real and t : integer -> integer, as well as the fixed
;; arbitrary region function and linked predicate.

(defstub frq-memory-at (memory-tag address) t)
(defstub frq-malloc-at (malloc-tag index) t)
(defstub frq-region-op (base) t)
(defstub frq-linked-op (malloc-tag) t)

(defun-sk frq-memory-function-p (ctx memory-tag)
  (forall (address)
    (implies
     (frq-address-p address)
     (frq-real-p
      ctx
      (frq-memory-at memory-tag address)))))

(defun-sk frq-malloc-function-p (malloc-tag)
  (forall (index)
    (implies
     (integerp index)
     (integerp (frq-malloc-at malloc-tag index)))))

(defun-sk frq-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (frq-region-op base)))))

(defun frq-linked-p (malloc-tag)
  (if (frq-linked-op malloc-tag) t nil))

(defun frq-valid-rw-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (< 0 (frq-address-base address))
    (<= 0 (frq-address-offset address))
    (<=
     (+ (frq-address-offset address) length)
     (frq-malloc-at
      malloc-tag
      (frq-address-base address))))))

(defun frq-valid-rd-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (frq-address-base address)))
    (<= 0 (frq-address-offset address))
    (<=
     (+ (frq-address-offset address) length)
     (frq-malloc-at
      malloc-tag
      (frq-address-base address))))))

(defun frq-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (frq-address-base left)
     (frq-address-base right)))
   (<=
    (+ (frq-address-offset right) right-length)
    (frq-address-offset left))
   (<=
    (+ (frq-address-offset left) left-length)
    (frq-address-offset right))))

;; An update list is newest first. Assoc-equal therefore gives exactly the
;; source's successive Function.update semantics, including address aliasing.

(defun frq-memory-read (memory-tag updates address)
  (let ((entry (assoc-equal address updates)))
    (if entry
        (cdr entry)
      (frq-memory-at memory-tag address))))

(defun frq-memory-write (updates address value)
  (cons (cons address value) updates))

;; In the imported source theory is_float32 is definitionally true, while the
;; supplied classification axiom makes is_finite32 true for every real.

(defun frq-is-float32-p (value)
  (declare (ignore value))
  t)

(defun frq-is-finite32-p (value)
  (declare (ignore value))
  t)

(defun frq-finite-floatquat-p
    (memory-tag updates address)
  (and
   (frq-is-finite32-p
    (frq-memory-read
     memory-tag updates (frq-shift address 0)))
   (frq-is-finite32-p
    (frq-memory-read
     memory-tag updates (frq-shift address 1)))
   (frq-is-finite32-p
    (frq-memory-read
     memory-tag updates (frq-shift address 2)))
   (frq-is-finite32-p
    (frq-memory-read
     memory-tag updates (frq-shift address 3)))))

(defun frq-rvalid-floatquat-p
    (malloc-tag memory-tag updates address)
  (and
   (frq-finite-floatquat-p memory-tag updates address)
   (frq-valid-rd-p malloc-tag address 4)))

(defun frq-unitary-quaternion-p
    (ctx one memory-tag updates address)
  (let*
      ((q0
        (frq-memory-read
         memory-tag updates (frq-shift address 0)))
       (q1
        (frq-memory-read
         memory-tag updates (frq-shift address 1)))
       (q2
        (frq-memory-read
         memory-tag updates (frq-shift address 2)))
       (q3
        (frq-memory-read
         memory-tag updates (frq-shift address 3))))
    (equal
     (frq-add
      ctx
      (frq-add
       ctx
       (frq-add
        ctx
        (frq-mul ctx q0 q0)
        (frq-mul ctx q1 q1))
       (frq-mul ctx q2 q2))
      (frq-mul ctx q3 q3))
     one)))

;; Matrices are row-major nine-tuples, exactly matching the source record.
;; Transposition, quaternion conversion, and entrywise equality unfold the
;; corresponding source definitions.

(defun frq-matrix
    (a00 a01 a02 a10 a11 a12 a20 a21 a22)
  (list a00 a01 a02 a10 a11 a12 a20 a21 a22))

(defun frq-matrix-entry (matrix row column)
  (nth (+ (* 3 row) column) matrix))

(defun frq-matrix-of-memory
    (memory-tag updates address)
  (let ((base (frq-shift address 0)))
    (frq-matrix
     (frq-memory-read
      memory-tag updates (frq-shift base 0))
     (frq-memory-read
      memory-tag updates (frq-shift base 1))
     (frq-memory-read
      memory-tag updates (frq-shift base 2))
     (frq-memory-read
      memory-tag updates (frq-shift base 3))
     (frq-memory-read
      memory-tag updates (frq-shift base 4))
     (frq-memory-read
      memory-tag updates (frq-shift base 5))
     (frq-memory-read
      memory-tag updates (frq-shift base 6))
     (frq-memory-read
      memory-tag updates (frq-shift base 7))
     (frq-memory-read
      memory-tag updates (frq-shift base 8)))))

(defun frq-matrix-transpose (matrix)
  (frq-matrix
   (frq-matrix-entry matrix 0 0)
   (frq-matrix-entry matrix 1 0)
   (frq-matrix-entry matrix 2 0)
   (frq-matrix-entry matrix 0 1)
   (frq-matrix-entry matrix 1 1)
   (frq-matrix-entry matrix 2 1)
   (frq-matrix-entry matrix 0 2)
   (frq-matrix-entry matrix 1 2)
   (frq-matrix-entry matrix 2 2)))

(defun frq-quaternion-matrix
    (ctx one memory-tag updates address)
  (let*
      ((r
        (frq-memory-read
         memory-tag updates (frq-shift address 2)))
       (r-1 (frq-mul ctx r r))
       (r-2 (frq-neg ctx r-1))
       (r-3
        (frq-memory-read
         memory-tag updates (frq-shift address 3)))
       (r-4 (frq-mul ctx r-3 r-3))
       (r-5 (frq-neg ctx r-4))
       (r-6
        (frq-memory-read
         memory-tag updates (frq-shift address 0)))
       (r-7 (frq-mul ctx r-6 r-6))
       (r-8
        (frq-memory-read
         memory-tag updates (frq-shift address 1)))
       (r-9 (frq-mul ctx r-8 r-8))
       (r-10 (frq-mul ctx r-6 r-3))
       (r-11 (frq-mul ctx r-8 r))
       (r-12 (frq-mul ctx r-6 r))
       (r-13 (frq-mul ctx r-8 r-3))
       (r-14 (frq-neg ctx r-9))
       (r-15 (frq-mul ctx r-6 r-8))
       (r-16 (frq-mul ctx r r-3))
       (two (frq-two ctx one)))
    (frq-matrix
     (frq-add
      ctx
      (frq-add
       ctx
       (frq-add ctx r-7 r-9)
       r-2)
      r-5)
     (frq-mul
      ctx two (frq-add ctx r-11 (frq-neg ctx r-10)))
     (frq-mul ctx two (frq-add ctx r-12 r-13))
     (frq-mul ctx two (frq-add ctx r-10 r-11))
     (frq-add
      ctx
      (frq-add
       ctx
       (frq-add ctx r-7 r-1)
       r-14)
      r-5)
     (frq-mul
      ctx two (frq-add ctx r-16 (frq-neg ctx r-15)))
     (frq-mul
      ctx two (frq-add ctx r-13 (frq-neg ctx r-12)))
     (frq-mul ctx two (frq-add ctx r-15 r-16))
     (frq-add
      ctx
      (frq-add
       ctx
       (frq-add ctx r-7 r-4)
       r-14)
      r-2))))

(defun frq-matrix-equal-p (left right)
  (and
   (equal
    (frq-matrix-entry left 0 0)
    (frq-matrix-entry right 0 0))
   (equal
    (frq-matrix-entry left 0 1)
    (frq-matrix-entry right 0 1))
   (equal
    (frq-matrix-entry left 0 2)
    (frq-matrix-entry right 0 2))
   (equal
    (frq-matrix-entry left 1 0)
    (frq-matrix-entry right 1 0))
   (equal
    (frq-matrix-entry left 1 1)
    (frq-matrix-entry right 1 1))
   (equal
    (frq-matrix-entry left 1 2)
    (frq-matrix-entry right 1 2))
   (equal
    (frq-matrix-entry left 2 0)
    (frq-matrix-entry right 2 0))
   (equal
    (frq-matrix-entry left 2 1)
    (frq-matrix-entry right 2 1))
   (equal
    (frq-matrix-entry left 2 2)
    (frq-matrix-entry right 2 2))))

(defun-sk
    ntp4vc-float-rmat-of-quat-post-goal0-statement ()
  (forall
   (ctx zero one a-1 a memory-tag malloc-tag)
   (implies
    (and
     (frq-real-context-p ctx zero one)
     (frq-address-p a-1)
     (frq-address-p a)
     (frq-memory-function-p ctx memory-tag)
     (frq-malloc-function-p malloc-tag)
     (frq-region-function-p))
    (let*
        ((updates-0 nil)
         (r
          (frq-memory-read
           memory-tag updates-0 (frq-shift a-1 0)))
         (r-1
          (frq-memory-read
           memory-tag updates-0 (frq-shift a-1 1)))
         (r-2
          (frq-memory-read
           memory-tag updates-0 (frq-shift a-1 2)))
         (r-3
          (frq-memory-read
           memory-tag updates-0 (frq-shift a-1 3)))
         (two (frq-two ctx one))
         (r-4 (frq-mul ctx two r))
         (r-5 (frq-mul ctx two r-1))
         (r-6 (frq-mul ctx two r-3))
         (r-7 (frq-mul ctx r-4 r-1))
         (r-8 (frq-mul ctx r-4 r-2))
         (r-9 (frq-mul ctx r-4 r-3))
         (r-10 (frq-mul ctx r-5 r-2))
         (r-11 (frq-mul ctx r-5 r-3))
         (r-12 (frq-mul ctx r-2 r-6))
         (r-13
          (frq-add
           ctx
           (frq-mul ctx r-4 r)
           (frq-neg ctx one)))
         (a-2 (frq-shift a 0))
         (updates-1
          (frq-memory-write
           updates-0
           (frq-shift a-2 0)
           (frq-add
            ctx r-13 (frq-mul ctx r-5 r-1))))
         (updates-2
          (frq-memory-write
           updates-1
           (frq-shift a-2 1)
           (frq-add ctx r-10 r-9)))
         (updates-3
          (frq-memory-write
           updates-2
           (frq-shift a-2 2)
           (frq-add ctx r-11 (frq-neg ctx r-8))))
         (updates-4
          (frq-memory-write
           updates-3
           (frq-shift a-2 3)
           (frq-add ctx r-10 (frq-neg ctx r-9))))
         (updates-5
          (frq-memory-write
           updates-4
           (frq-shift a-2 4)
           (frq-add
            ctx
            r-13
            (frq-mul
             ctx
             (frq-mul ctx two r-2)
             r-2))))
         (updates-6
          (frq-memory-write
           updates-5
           (frq-shift a-2 5)
           (frq-add ctx r-12 r-7)))
         (updates-7
          (frq-memory-write
           updates-6
           (frq-shift a-2 6)
           (frq-add ctx r-11 r-8)))
         (updates-8
          (frq-memory-write
           updates-7
           (frq-shift a-2 7)
           (frq-add ctx r-12 (frq-neg ctx r-7))))
         (updates-9
          (frq-memory-write
           updates-8
           (frq-shift a-2 8)
           (frq-add
            ctx r-13 (frq-mul ctx r-6 r-3)))))
      (implies
       (and
        (<= (frq-region-op (frq-address-base a)) 0)
        (<= (frq-region-op (frq-address-base a-1)) 0)
        (frq-linked-p malloc-tag)
        (frq-unitary-quaternion-p
         ctx one memory-tag updates-0 a-1)
        (frq-valid-rw-p malloc-tag a 9)
        (frq-rvalid-floatquat-p
         malloc-tag memory-tag updates-0 a-1)
        (frq-separated-p a 9 a-1 4)
        (frq-is-float32-p r)
        (frq-is-float32-p r-1)
        (frq-is-float32-p r-2)
        (frq-is-float32-p r-3)
        (frq-is-float32-p r-4)
        (frq-is-float32-p r-5)
        (frq-is-float32-p r-6)
        (frq-is-float32-p r-7)
        (frq-is-float32-p r-8)
        (frq-is-float32-p r-9)
        (frq-is-float32-p r-10)
        (frq-is-float32-p r-11)
        (frq-is-float32-p r-12)
        (frq-is-float32-p r-13))
       (frq-matrix-equal-p
        (frq-matrix-transpose
         (frq-matrix-of-memory
          memory-tag updates-9 a))
        (frq-quaternion-matrix
         ctx one memory-tag updates-9 a-1)))))))

(value-triple :itpeval-statement-checked)

:q
