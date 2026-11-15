;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/airborne/float_rmat_of_eulers_321/float_rmat_of_eulers_321_Why3_ide_VCfloat_rmat_of_eulers_321_post_goal0:
;; the nine real entries computed from 3-2-1 Euler-angle sines and cosines
;; form an orthogonal 3-by-3 rotation matrix under the stated memory and
;; floating-point-model hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars range over an arbitrary real closed ordered field. Real closed
;; fields have the same first-order ordered-field theory as the mathematical
;; reals, so this does not restrict source reals to ACL2 rationals. The sine
;; and cosine interface includes the exact circle identity used by this VC.

(defstub rfe321g0-real-op (ctx x) t)
(defstub rfe321g0-add-op (ctx x y) t)
(defstub rfe321g0-mul-op (ctx x y) t)
(defstub rfe321g0-neg-op (ctx x) t)
(defstub rfe321g0-inv-op (ctx x) t)
(defstub rfe321g0-lt-op (ctx x y) t)
(defstub rfe321g0-sin-op (ctx x) t)
(defstub rfe321g0-cos-op (ctx x) t)

(defun rfe321g0-real-p (ctx x)
  (if (rfe321g0-real-op ctx x) t nil))

(defun rfe321g0-add (ctx x y)
  (rfe321g0-add-op ctx x y))

(defun rfe321g0-mul (ctx x y)
  (rfe321g0-mul-op ctx x y))

(defun rfe321g0-neg (ctx x)
  (rfe321g0-neg-op ctx x))

(defun rfe321g0-inv (ctx x)
  (rfe321g0-inv-op ctx x))

(defun rfe321g0-lt (ctx x y)
  (if (rfe321g0-lt-op ctx x y) t nil))

(defun rfe321g0-le (ctx x y)
  (not (rfe321g0-lt ctx y x)))

(defun rfe321g0-sin (ctx x)
  (rfe321g0-sin-op ctx x))

(defun rfe321g0-cos (ctx x)
  (rfe321g0-cos-op ctx x))

(defun-sk rfe321g0-field-laws-p (ctx zero one)
  (forall (x y z)
    (implies
     (and
      (rfe321g0-real-p ctx x)
      (rfe321g0-real-p ctx y)
      (rfe321g0-real-p ctx z))
     (and
      (rfe321g0-real-p ctx (rfe321g0-add ctx x y))
      (rfe321g0-real-p ctx (rfe321g0-mul ctx x y))
      (rfe321g0-real-p ctx (rfe321g0-neg ctx x))
      (rfe321g0-real-p ctx (rfe321g0-inv ctx x))
      (equal
       (rfe321g0-add ctx (rfe321g0-add ctx x y) z)
       (rfe321g0-add ctx x (rfe321g0-add ctx y z)))
      (equal (rfe321g0-add ctx x y) (rfe321g0-add ctx y x))
      (equal (rfe321g0-add ctx x zero) x)
      (equal (rfe321g0-add ctx x (rfe321g0-neg ctx x)) zero)
      (equal
       (rfe321g0-mul ctx (rfe321g0-mul ctx x y) z)
       (rfe321g0-mul ctx x (rfe321g0-mul ctx y z)))
      (equal (rfe321g0-mul ctx x y) (rfe321g0-mul ctx y x))
      (equal (rfe321g0-mul ctx x one) x)
      (equal (rfe321g0-inv ctx zero) zero)
      (implies
       (not (equal x zero))
       (equal (rfe321g0-mul ctx x (rfe321g0-inv ctx x)) one))
      (equal
       (rfe321g0-mul ctx x (rfe321g0-add ctx y z))
       (rfe321g0-add
        ctx
        (rfe321g0-mul ctx x y)
        (rfe321g0-mul ctx x z)))))))

(defun-sk rfe321g0-order-laws-p (ctx zero)
  (forall (x y z)
    (implies
     (and
      (rfe321g0-real-p ctx x)
      (rfe321g0-real-p ctx y)
      (rfe321g0-real-p ctx z))
     (and
      (not (rfe321g0-lt ctx x x))
      (or
       (equal x y)
       (rfe321g0-lt ctx x y)
       (rfe321g0-lt ctx y x))
      (implies
       (and (rfe321g0-lt ctx x y) (rfe321g0-lt ctx y z))
       (rfe321g0-lt ctx x z))
      (implies
       (rfe321g0-lt ctx x y)
       (rfe321g0-lt
        ctx
        (rfe321g0-add ctx x z)
        (rfe321g0-add ctx y z)))
      (implies
       (and (rfe321g0-lt ctx zero x) (rfe321g0-lt ctx zero y))
       (rfe321g0-lt ctx zero (rfe321g0-mul ctx x y)))))))

(defun-sk rfe321g0-positive-square-root-exists-p
    (ctx zero x)
  (exists (root)
    (and
     (rfe321g0-real-p ctx root)
     (rfe321g0-le ctx zero root)
     (equal (rfe321g0-mul ctx root root) x))))

(defun-sk rfe321g0-positive-square-root-laws-p (ctx zero)
  (forall (x)
    (implies
     (and
      (rfe321g0-real-p ctx x)
      (rfe321g0-lt ctx zero x))
     (rfe321g0-positive-square-root-exists-p ctx zero x))))

(defun rfe321g0-real-coefficient-list-p (ctx coefficients)
  (if (consp coefficients)
      (and
       (rfe321g0-real-p ctx (car coefficients))
       (rfe321g0-real-coefficient-list-p ctx (cdr coefficients)))
    (equal coefficients nil)))

(defun rfe321g0-poly-eval (ctx zero coefficients x)
  (if (consp coefficients)
      (rfe321g0-add
       ctx
       (car coefficients)
       (rfe321g0-mul
        ctx
        x
        (rfe321g0-poly-eval ctx zero (cdr coefficients) x)))
    zero))

(defun-sk rfe321g0-odd-polynomial-root-exists-p
    (ctx zero coefficients)
  (exists (root)
    (and
     (rfe321g0-real-p ctx root)
     (equal
      (rfe321g0-poly-eval ctx zero coefficients root)
      zero))))

(defun-sk rfe321g0-odd-root-laws-p (ctx zero)
  (forall (coefficients degree)
    (implies
     (and
      (natp degree)
      (not (equal degree 0))
      (oddp degree)
      (true-listp coefficients)
      (consp coefficients)
      (equal (len coefficients) (+ 1 degree))
      (rfe321g0-real-coefficient-list-p ctx coefficients)
      (not (equal (car (last coefficients)) zero)))
     (rfe321g0-odd-polynomial-root-exists-p
      ctx zero coefficients))))

(defun-sk rfe321g0-trigonometric-laws-p (ctx one)
  (forall (x)
    (implies
     (rfe321g0-real-p ctx x)
     (and
      (rfe321g0-real-p ctx (rfe321g0-sin ctx x))
      (rfe321g0-real-p ctx (rfe321g0-cos ctx x))
      (equal
       (rfe321g0-add
        ctx
        (rfe321g0-mul
         ctx
         (rfe321g0-sin ctx x)
         (rfe321g0-sin ctx x))
        (rfe321g0-mul
         ctx
         (rfe321g0-cos ctx x)
         (rfe321g0-cos ctx x)))
       one)))))

(defun rfe321g0-real-context-p (ctx zero one)
  (and
   (rfe321g0-real-p ctx zero)
   (rfe321g0-real-p ctx one)
   (not (equal zero one))
   (rfe321g0-lt ctx zero one)
   (rfe321g0-field-laws-p ctx zero one)
   (rfe321g0-order-laws-p ctx zero)
   (rfe321g0-positive-square-root-laws-p ctx zero)
   (rfe321g0-odd-root-laws-p ctx zero)
   (rfe321g0-trigonometric-laws-p ctx one)))

;; Addresses are exactly pairs of mathematical integers, matching the source
;; record with integer base and offset fields.

(defun rfe321g0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun rfe321g0-address-base (address)
  (car address))

(defun rfe321g0-address-offset (address)
  (cdr address))

(defun rfe321g0-shift (address amount)
  (cons
   (rfe321g0-address-base address)
   (+ (rfe321g0-address-offset address) amount)))

;; Tagged conservative interfaces preserve the arbitrary source functions
;; t_1 : address -> real and t : integer -> integer, as well as the fixed
;; arbitrary region function and linked predicate.

(defstub rfe321g0-memory-at (memory-tag address) t)
(defstub rfe321g0-malloc-at (malloc-tag index) t)
(defstub rfe321g0-region-op (base) t)
(defstub rfe321g0-linked-op (malloc-tag) t)

(defun-sk rfe321g0-memory-function-p (ctx memory-tag)
  (forall (address)
    (implies
     (rfe321g0-address-p address)
     (rfe321g0-real-p
      ctx
      (rfe321g0-memory-at memory-tag address)))))

(defun-sk rfe321g0-malloc-function-p (malloc-tag)
  (forall (index)
    (implies
     (integerp index)
     (integerp (rfe321g0-malloc-at malloc-tag index)))))

(defun-sk rfe321g0-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (rfe321g0-region-op base)))))

(defun rfe321g0-linked-p (malloc-tag)
  (if (rfe321g0-linked-op malloc-tag) t nil))

(defun rfe321g0-valid-rw-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (< 0 (rfe321g0-address-base address))
    (<= 0 (rfe321g0-address-offset address))
    (<=
     (+ (rfe321g0-address-offset address) length)
     (rfe321g0-malloc-at
      malloc-tag
      (rfe321g0-address-base address))))))

(defun rfe321g0-valid-rd-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (rfe321g0-address-base address)))
    (<= 0 (rfe321g0-address-offset address))
    (<=
     (+ (rfe321g0-address-offset address) length)
     (rfe321g0-malloc-at
      malloc-tag
      (rfe321g0-address-base address))))))

;; An update list is newest first. Assoc-equal therefore gives exactly the
;; source's successive Function.update semantics, including address aliasing.

(defun rfe321g0-memory-read (memory-tag updates address)
  (let ((entry (assoc-equal address updates)))
    (if entry
        (cdr entry)
      (rfe321g0-memory-at memory-tag address))))

(defun rfe321g0-memory-write (updates address value)
  (cons (cons address value) updates))

;; In the imported source theory is_float32 is definitionally true, while the
;; supplied classification axiom makes is_finite32 true for every real.

(defun rfe321g0-is-float32-p (value)
  (declare (ignore value))
  t)

(defun rfe321g0-is-finite32-p (value)
  (declare (ignore value))
  t)

(defun rfe321g0-finite-floateulers-p
    (memory-tag updates address)
  (and
   (rfe321g0-is-finite32-p
    (rfe321g0-memory-read
     memory-tag updates (rfe321g0-shift address 0)))
   (rfe321g0-is-finite32-p
    (rfe321g0-memory-read
     memory-tag updates (rfe321g0-shift address 2)))
   (rfe321g0-is-finite32-p
    (rfe321g0-memory-read
     memory-tag updates (rfe321g0-shift address 1)))))

(defun rfe321g0-rvalid-floateulers-p
    (malloc-tag memory-tag updates address)
  (and
   (rfe321g0-finite-floateulers-p
    memory-tag updates address)
   (rfe321g0-valid-rd-p malloc-tag address 3)))

;; Matrices are row-major nine-tuples, exactly matching the source record.
;; Multiplication, transposition, and entrywise equality unfold the source
;; definitions of p_rotation_matrix.

(defun rfe321g0-matrix
    (a00 a01 a02 a10 a11 a12 a20 a21 a22)
  (list a00 a01 a02 a10 a11 a12 a20 a21 a22))

(defun rfe321g0-matrix-entry (matrix row column)
  (nth (+ (* 3 row) column) matrix))

(defun rfe321g0-matrix-of-memory
    (memory-tag updates address)
  (let ((base (rfe321g0-shift address 0)))
    (rfe321g0-matrix
     (rfe321g0-memory-read
      memory-tag updates (rfe321g0-shift base 0))
     (rfe321g0-memory-read
      memory-tag updates (rfe321g0-shift base 1))
     (rfe321g0-memory-read
      memory-tag updates (rfe321g0-shift base 2))
     (rfe321g0-memory-read
      memory-tag updates (rfe321g0-shift base 3))
     (rfe321g0-memory-read
      memory-tag updates (rfe321g0-shift base 4))
     (rfe321g0-memory-read
      memory-tag updates (rfe321g0-shift base 5))
     (rfe321g0-memory-read
      memory-tag updates (rfe321g0-shift base 6))
     (rfe321g0-memory-read
      memory-tag updates (rfe321g0-shift base 7))
     (rfe321g0-memory-read
      memory-tag updates (rfe321g0-shift base 8)))))

(defun rfe321g0-matrix-transpose (matrix)
  (rfe321g0-matrix
   (rfe321g0-matrix-entry matrix 0 0)
   (rfe321g0-matrix-entry matrix 1 0)
   (rfe321g0-matrix-entry matrix 2 0)
   (rfe321g0-matrix-entry matrix 0 1)
   (rfe321g0-matrix-entry matrix 1 1)
   (rfe321g0-matrix-entry matrix 2 1)
   (rfe321g0-matrix-entry matrix 0 2)
   (rfe321g0-matrix-entry matrix 1 2)
   (rfe321g0-matrix-entry matrix 2 2)))

(defun rfe321g0-dot3 (ctx a b c d e f)
  (rfe321g0-add
   ctx
   (rfe321g0-add
    ctx
    (rfe321g0-mul ctx a b)
    (rfe321g0-mul ctx c d))
   (rfe321g0-mul ctx e f)))

(defun rfe321g0-matrix-multiply (ctx left right)
  (rfe321g0-matrix
   (rfe321g0-dot3
    ctx
    (rfe321g0-matrix-entry left 0 0)
    (rfe321g0-matrix-entry right 0 0)
    (rfe321g0-matrix-entry left 0 1)
    (rfe321g0-matrix-entry right 1 0)
    (rfe321g0-matrix-entry left 0 2)
    (rfe321g0-matrix-entry right 2 0))
   (rfe321g0-dot3
    ctx
    (rfe321g0-matrix-entry left 0 0)
    (rfe321g0-matrix-entry right 0 1)
    (rfe321g0-matrix-entry left 0 1)
    (rfe321g0-matrix-entry right 1 1)
    (rfe321g0-matrix-entry left 0 2)
    (rfe321g0-matrix-entry right 2 1))
   (rfe321g0-dot3
    ctx
    (rfe321g0-matrix-entry left 0 0)
    (rfe321g0-matrix-entry right 0 2)
    (rfe321g0-matrix-entry left 0 1)
    (rfe321g0-matrix-entry right 1 2)
    (rfe321g0-matrix-entry left 0 2)
    (rfe321g0-matrix-entry right 2 2))
   (rfe321g0-dot3
    ctx
    (rfe321g0-matrix-entry left 1 0)
    (rfe321g0-matrix-entry right 0 0)
    (rfe321g0-matrix-entry left 1 1)
    (rfe321g0-matrix-entry right 1 0)
    (rfe321g0-matrix-entry left 1 2)
    (rfe321g0-matrix-entry right 2 0))
   (rfe321g0-dot3
    ctx
    (rfe321g0-matrix-entry left 1 0)
    (rfe321g0-matrix-entry right 0 1)
    (rfe321g0-matrix-entry left 1 1)
    (rfe321g0-matrix-entry right 1 1)
    (rfe321g0-matrix-entry left 1 2)
    (rfe321g0-matrix-entry right 2 1))
   (rfe321g0-dot3
    ctx
    (rfe321g0-matrix-entry left 1 0)
    (rfe321g0-matrix-entry right 0 2)
    (rfe321g0-matrix-entry left 1 1)
    (rfe321g0-matrix-entry right 1 2)
    (rfe321g0-matrix-entry left 1 2)
    (rfe321g0-matrix-entry right 2 2))
   (rfe321g0-dot3
    ctx
    (rfe321g0-matrix-entry left 2 0)
    (rfe321g0-matrix-entry right 0 0)
    (rfe321g0-matrix-entry left 2 1)
    (rfe321g0-matrix-entry right 1 0)
    (rfe321g0-matrix-entry left 2 2)
    (rfe321g0-matrix-entry right 2 0))
   (rfe321g0-dot3
    ctx
    (rfe321g0-matrix-entry left 2 0)
    (rfe321g0-matrix-entry right 0 1)
    (rfe321g0-matrix-entry left 2 1)
    (rfe321g0-matrix-entry right 1 1)
    (rfe321g0-matrix-entry left 2 2)
    (rfe321g0-matrix-entry right 2 1))
   (rfe321g0-dot3
    ctx
    (rfe321g0-matrix-entry left 2 0)
    (rfe321g0-matrix-entry right 0 2)
    (rfe321g0-matrix-entry left 2 1)
    (rfe321g0-matrix-entry right 1 2)
    (rfe321g0-matrix-entry left 2 2)
    (rfe321g0-matrix-entry right 2 2))))

(defun rfe321g0-matrix-equal-p (left right)
  (and
   (equal
    (rfe321g0-matrix-entry left 0 0)
    (rfe321g0-matrix-entry right 0 0))
   (equal
    (rfe321g0-matrix-entry left 0 1)
    (rfe321g0-matrix-entry right 0 1))
   (equal
    (rfe321g0-matrix-entry left 0 2)
    (rfe321g0-matrix-entry right 0 2))
   (equal
    (rfe321g0-matrix-entry left 1 0)
    (rfe321g0-matrix-entry right 1 0))
   (equal
    (rfe321g0-matrix-entry left 1 1)
    (rfe321g0-matrix-entry right 1 1))
   (equal
    (rfe321g0-matrix-entry left 1 2)
    (rfe321g0-matrix-entry right 1 2))
   (equal
    (rfe321g0-matrix-entry left 2 0)
    (rfe321g0-matrix-entry right 2 0))
   (equal
    (rfe321g0-matrix-entry left 2 1)
    (rfe321g0-matrix-entry right 2 1))
   (equal
    (rfe321g0-matrix-entry left 2 2)
    (rfe321g0-matrix-entry right 2 2))))

(defun rfe321g0-rotation-matrix-p (ctx zero one matrix)
  (rfe321g0-matrix-equal-p
   (rfe321g0-matrix-multiply
    ctx matrix (rfe321g0-matrix-transpose matrix))
   (rfe321g0-matrix
    one zero zero
    zero one zero
    zero zero one)))

(defun-sk
    ntp4vc-float-rmat-of-eulers-321-post-goal0-statement ()
  (forall
   (ctx zero one a-1 a memory-tag malloc-tag)
   (implies
    (and
     (rfe321g0-real-context-p ctx zero one)
     (rfe321g0-address-p a-1)
     (rfe321g0-address-p a)
     (rfe321g0-memory-function-p ctx memory-tag)
     (rfe321g0-malloc-function-p malloc-tag)
     (rfe321g0-region-function-p))
    (let*
        ((updates-0 nil)
         (r
          (rfe321g0-memory-read
           memory-tag updates-0 (rfe321g0-shift a-1 0)))
         (r-1 (rfe321g0-sin ctx r))
         (r-2
          (rfe321g0-memory-read
           memory-tag updates-0 (rfe321g0-shift a-1 2)))
         (r-3 (rfe321g0-sin ctx r-2))
         (r-4
          (rfe321g0-memory-read
           memory-tag updates-0 (rfe321g0-shift a-1 1)))
         (r-5 (rfe321g0-sin ctx r-4))
         (r-6 (rfe321g0-cos ctx r))
         (r-7 (rfe321g0-cos ctx r-2))
         (r-8 (rfe321g0-cos ctx r-4))
         (a-2 (rfe321g0-shift a 0))
         (r-9 (rfe321g0-mul ctx r-1 r-5))
         (r-10 (rfe321g0-mul ctx r-6 r-5))
         (updates-1
          (rfe321g0-memory-write
           updates-0
           (rfe321g0-shift a-2 0)
           (rfe321g0-mul ctx r-8 r-7)))
         (updates-2
          (rfe321g0-memory-write
           updates-1
           (rfe321g0-shift a-2 1)
           (rfe321g0-mul ctx r-8 r-3)))
         (updates-3
          (rfe321g0-memory-write
           updates-2
           (rfe321g0-shift a-2 2)
           (rfe321g0-neg ctx r-5)))
         (updates-4
          (rfe321g0-memory-write
           updates-3
           (rfe321g0-shift a-2 3)
           (rfe321g0-add
            ctx
            (rfe321g0-mul ctx r-9 r-7)
            (rfe321g0-neg
             ctx
             (rfe321g0-mul ctx r-6 r-3)))))
         (updates-5
          (rfe321g0-memory-write
           updates-4
           (rfe321g0-shift a-2 4)
           (rfe321g0-add
            ctx
            (rfe321g0-mul ctx r-9 r-3)
            (rfe321g0-mul ctx r-6 r-7))))
         (updates-6
          (rfe321g0-memory-write
           updates-5
           (rfe321g0-shift a-2 5)
           (rfe321g0-mul ctx r-1 r-8)))
         (updates-7
          (rfe321g0-memory-write
           updates-6
           (rfe321g0-shift a-2 6)
           (rfe321g0-add
            ctx
            (rfe321g0-mul ctx r-10 r-7)
            (rfe321g0-mul ctx r-1 r-3))))
         (updates-8
          (rfe321g0-memory-write
           updates-7
           (rfe321g0-shift a-2 7)
           (rfe321g0-add
            ctx
            (rfe321g0-mul ctx r-10 r-3)
            (rfe321g0-neg
             ctx
             (rfe321g0-mul ctx r-1 r-7)))))
         (updates-9
          (rfe321g0-memory-write
           updates-8
           (rfe321g0-shift a-2 8)
           (rfe321g0-mul ctx r-6 r-8))))
      (implies
       (and
        (<= (rfe321g0-region-op (rfe321g0-address-base a)) 0)
        (<= (rfe321g0-region-op (rfe321g0-address-base a-1)) 0)
        (rfe321g0-le ctx r-1 one)
        (rfe321g0-le ctx r-3 one)
        (rfe321g0-le ctx r-5 one)
        (rfe321g0-le ctx r-6 one)
        (rfe321g0-le ctx r-7 one)
        (rfe321g0-le ctx r-8 one)
        (rfe321g0-le ctx (rfe321g0-neg ctx one) r-1)
        (rfe321g0-le ctx (rfe321g0-neg ctx one) r-3)
        (rfe321g0-le ctx (rfe321g0-neg ctx one) r-5)
        (rfe321g0-le ctx (rfe321g0-neg ctx one) r-6)
        (rfe321g0-le ctx (rfe321g0-neg ctx one) r-7)
        (rfe321g0-le ctx (rfe321g0-neg ctx one) r-8)
        (rfe321g0-linked-p malloc-tag)
        (rfe321g0-valid-rw-p malloc-tag a 9)
        (rfe321g0-rvalid-floateulers-p
         malloc-tag memory-tag updates-0 a-1)
        (rfe321g0-is-finite32-p r)
        (rfe321g0-is-finite32-p r-2)
        (rfe321g0-is-finite32-p r-4)
        (rfe321g0-is-float32-p r)
        (rfe321g0-is-float32-p r-2)
        (rfe321g0-is-float32-p r-4)
        (rfe321g0-is-finite32-p r-1)
        (rfe321g0-is-finite32-p r-3)
        (rfe321g0-is-finite32-p r-5)
        (rfe321g0-is-finite32-p r-6)
        (rfe321g0-is-finite32-p r-7)
        (rfe321g0-is-finite32-p r-8)
        (rfe321g0-is-float32-p r-1)
        (rfe321g0-is-float32-p r-3)
        (rfe321g0-is-float32-p r-5)
        (rfe321g0-is-float32-p r-6)
        (rfe321g0-is-float32-p r-7)
        (rfe321g0-is-float32-p r-8))
       (rfe321g0-rotation-matrix-p
        ctx
        zero
        one
        (rfe321g0-matrix-of-memory
         memory-tag updates-9 a)))))))

(value-triple :itpeval-statement-checked)

:q
