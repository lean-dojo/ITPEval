;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/airborne/float_rmat_of_eulers_312/float_rmat_of_eulers_312_Why3_ide_VCfloat_rmat_of_eulers_312_post_goal0:
;; the nine real entries computed from 3-1-2 Euler-angle sines and cosines
;; form an orthogonal 3-by-3 rotation matrix under the stated memory and
;; floating-point-model hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars range over an arbitrary real closed ordered field. Real closed
;; fields have the same first-order ordered-field theory as the mathematical
;; reals, so this does not restrict source reals to ACL2 rationals. The sine
;; and cosine interface includes the exact circle identity used by this VC.

(defstub rfe312-real-op (ctx x) t)
(defstub rfe312-add-op (ctx x y) t)
(defstub rfe312-mul-op (ctx x y) t)
(defstub rfe312-neg-op (ctx x) t)
(defstub rfe312-inv-op (ctx x) t)
(defstub rfe312-lt-op (ctx x y) t)
(defstub rfe312-sin-op (ctx x) t)
(defstub rfe312-cos-op (ctx x) t)

(defun rfe312-real-p (ctx x)
  (if (rfe312-real-op ctx x) t nil))

(defun rfe312-add (ctx x y)
  (rfe312-add-op ctx x y))

(defun rfe312-mul (ctx x y)
  (rfe312-mul-op ctx x y))

(defun rfe312-neg (ctx x)
  (rfe312-neg-op ctx x))

(defun rfe312-inv (ctx x)
  (rfe312-inv-op ctx x))

(defun rfe312-lt (ctx x y)
  (if (rfe312-lt-op ctx x y) t nil))

(defun rfe312-le (ctx x y)
  (not (rfe312-lt ctx y x)))

(defun rfe312-sin (ctx x)
  (rfe312-sin-op ctx x))

(defun rfe312-cos (ctx x)
  (rfe312-cos-op ctx x))

(defun-sk rfe312-field-laws-p (ctx zero one)
  (forall (x y z)
    (implies
     (and
      (rfe312-real-p ctx x)
      (rfe312-real-p ctx y)
      (rfe312-real-p ctx z))
     (and
      (rfe312-real-p ctx (rfe312-add ctx x y))
      (rfe312-real-p ctx (rfe312-mul ctx x y))
      (rfe312-real-p ctx (rfe312-neg ctx x))
      (rfe312-real-p ctx (rfe312-inv ctx x))
      (equal
       (rfe312-add ctx (rfe312-add ctx x y) z)
       (rfe312-add ctx x (rfe312-add ctx y z)))
      (equal (rfe312-add ctx x y) (rfe312-add ctx y x))
      (equal (rfe312-add ctx x zero) x)
      (equal (rfe312-add ctx x (rfe312-neg ctx x)) zero)
      (equal
       (rfe312-mul ctx (rfe312-mul ctx x y) z)
       (rfe312-mul ctx x (rfe312-mul ctx y z)))
      (equal (rfe312-mul ctx x y) (rfe312-mul ctx y x))
      (equal (rfe312-mul ctx x one) x)
      (equal (rfe312-inv ctx zero) zero)
      (implies
       (not (equal x zero))
       (equal (rfe312-mul ctx x (rfe312-inv ctx x)) one))
      (equal
       (rfe312-mul ctx x (rfe312-add ctx y z))
       (rfe312-add
        ctx
        (rfe312-mul ctx x y)
        (rfe312-mul ctx x z)))))))

(defun-sk rfe312-order-laws-p (ctx zero)
  (forall (x y z)
    (implies
     (and
      (rfe312-real-p ctx x)
      (rfe312-real-p ctx y)
      (rfe312-real-p ctx z))
     (and
      (not (rfe312-lt ctx x x))
      (or
       (equal x y)
       (rfe312-lt ctx x y)
       (rfe312-lt ctx y x))
      (implies
       (and (rfe312-lt ctx x y) (rfe312-lt ctx y z))
       (rfe312-lt ctx x z))
      (implies
       (rfe312-lt ctx x y)
       (rfe312-lt
        ctx
        (rfe312-add ctx x z)
        (rfe312-add ctx y z)))
      (implies
       (and (rfe312-lt ctx zero x) (rfe312-lt ctx zero y))
       (rfe312-lt ctx zero (rfe312-mul ctx x y)))))))

(defun-sk rfe312-positive-square-root-exists-p
    (ctx zero x)
  (exists (root)
    (and
     (rfe312-real-p ctx root)
     (rfe312-le ctx zero root)
     (equal (rfe312-mul ctx root root) x))))

(defun-sk rfe312-positive-square-root-laws-p (ctx zero)
  (forall (x)
    (implies
     (and
      (rfe312-real-p ctx x)
      (rfe312-lt ctx zero x))
     (rfe312-positive-square-root-exists-p ctx zero x))))

(defun rfe312-real-coefficient-list-p (ctx coefficients)
  (if (consp coefficients)
      (and
       (rfe312-real-p ctx (car coefficients))
       (rfe312-real-coefficient-list-p ctx (cdr coefficients)))
    (equal coefficients nil)))

(defun rfe312-poly-eval (ctx zero coefficients x)
  (if (consp coefficients)
      (rfe312-add
       ctx
       (car coefficients)
       (rfe312-mul
        ctx
        x
        (rfe312-poly-eval ctx zero (cdr coefficients) x)))
    zero))

(defun-sk rfe312-odd-polynomial-root-exists-p
    (ctx zero coefficients)
  (exists (root)
    (and
     (rfe312-real-p ctx root)
     (equal
      (rfe312-poly-eval ctx zero coefficients root)
      zero))))

(defun-sk rfe312-odd-root-laws-p (ctx zero)
  (forall (coefficients degree)
    (implies
     (and
      (natp degree)
      (not (equal degree 0))
      (oddp degree)
      (true-listp coefficients)
      (consp coefficients)
      (equal (len coefficients) (+ 1 degree))
      (rfe312-real-coefficient-list-p ctx coefficients)
      (not (equal (car (last coefficients)) zero)))
     (rfe312-odd-polynomial-root-exists-p
      ctx zero coefficients))))

(defun-sk rfe312-trigonometric-laws-p (ctx one)
  (forall (x)
    (implies
     (rfe312-real-p ctx x)
     (and
      (rfe312-real-p ctx (rfe312-sin ctx x))
      (rfe312-real-p ctx (rfe312-cos ctx x))
      (equal
       (rfe312-add
        ctx
        (rfe312-mul
         ctx
         (rfe312-sin ctx x)
         (rfe312-sin ctx x))
        (rfe312-mul
         ctx
         (rfe312-cos ctx x)
         (rfe312-cos ctx x)))
       one)))))

(defun rfe312-real-context-p (ctx zero one)
  (and
   (rfe312-real-p ctx zero)
   (rfe312-real-p ctx one)
   (not (equal zero one))
   (rfe312-lt ctx zero one)
   (rfe312-field-laws-p ctx zero one)
   (rfe312-order-laws-p ctx zero)
   (rfe312-positive-square-root-laws-p ctx zero)
   (rfe312-odd-root-laws-p ctx zero)
   (rfe312-trigonometric-laws-p ctx one)))

;; Addresses are exactly pairs of mathematical integers, matching the source
;; record with integer base and offset fields.

(defun rfe312-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun rfe312-address-base (address)
  (car address))

(defun rfe312-address-offset (address)
  (cdr address))

(defun rfe312-shift (address amount)
  (cons
   (rfe312-address-base address)
   (+ (rfe312-address-offset address) amount)))

;; Tagged conservative interfaces preserve the arbitrary source functions
;; t_1 : address -> real and t : integer -> integer, as well as the fixed
;; arbitrary region function and linked predicate.

(defstub rfe312-memory-at (memory-tag address) t)
(defstub rfe312-malloc-at (malloc-tag index) t)
(defstub rfe312-region-op (base) t)
(defstub rfe312-linked-op (malloc-tag) t)

(defun-sk rfe312-memory-function-p (ctx memory-tag)
  (forall (address)
    (implies
     (rfe312-address-p address)
     (rfe312-real-p
      ctx
      (rfe312-memory-at memory-tag address)))))

(defun-sk rfe312-malloc-function-p (malloc-tag)
  (forall (index)
    (implies
     (integerp index)
     (integerp (rfe312-malloc-at malloc-tag index)))))

(defun-sk rfe312-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (rfe312-region-op base)))))

(defun rfe312-linked-p (malloc-tag)
  (if (rfe312-linked-op malloc-tag) t nil))

(defun rfe312-valid-rw-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (< 0 (rfe312-address-base address))
    (<= 0 (rfe312-address-offset address))
    (<=
     (+ (rfe312-address-offset address) length)
     (rfe312-malloc-at
      malloc-tag
      (rfe312-address-base address))))))

(defun rfe312-valid-rd-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (rfe312-address-base address)))
    (<= 0 (rfe312-address-offset address))
    (<=
     (+ (rfe312-address-offset address) length)
     (rfe312-malloc-at
      malloc-tag
      (rfe312-address-base address))))))

;; An update list is newest first. Assoc-equal therefore gives exactly the
;; source's successive Function.update semantics, including address aliasing.

(defun rfe312-memory-read (memory-tag updates address)
  (let ((entry (assoc-equal address updates)))
    (if entry
        (cdr entry)
      (rfe312-memory-at memory-tag address))))

(defun rfe312-memory-write (updates address value)
  (cons (cons address value) updates))

;; In the imported source theory is_float32 is definitionally true, while the
;; supplied classification axiom makes is_finite32 true for every real.

(defun rfe312-is-float32-p (value)
  (declare (ignore value))
  t)

(defun rfe312-is-finite32-p (value)
  (declare (ignore value))
  t)

(defun rfe312-finite-floateulers-p
    (memory-tag updates address)
  (and
   (rfe312-is-finite32-p
    (rfe312-memory-read
     memory-tag updates (rfe312-shift address 0)))
   (rfe312-is-finite32-p
    (rfe312-memory-read
     memory-tag updates (rfe312-shift address 2)))
   (rfe312-is-finite32-p
    (rfe312-memory-read
     memory-tag updates (rfe312-shift address 1)))))

(defun rfe312-rvalid-floateulers-p
    (malloc-tag memory-tag updates address)
  (and
   (rfe312-finite-floateulers-p
    memory-tag updates address)
   (rfe312-valid-rd-p malloc-tag address 3)))

;; Matrices are row-major nine-tuples, exactly matching the source record.
;; Multiplication, transposition, and entrywise equality unfold the source
;; definitions of p_rotation_matrix.

(defun rfe312-matrix
    (a00 a01 a02 a10 a11 a12 a20 a21 a22)
  (list a00 a01 a02 a10 a11 a12 a20 a21 a22))

(defun rfe312-matrix-entry (matrix row column)
  (nth (+ (* 3 row) column) matrix))

(defun rfe312-matrix-of-memory
    (memory-tag updates address)
  (let ((base (rfe312-shift address 0)))
    (rfe312-matrix
     (rfe312-memory-read
      memory-tag updates (rfe312-shift base 0))
     (rfe312-memory-read
      memory-tag updates (rfe312-shift base 1))
     (rfe312-memory-read
      memory-tag updates (rfe312-shift base 2))
     (rfe312-memory-read
      memory-tag updates (rfe312-shift base 3))
     (rfe312-memory-read
      memory-tag updates (rfe312-shift base 4))
     (rfe312-memory-read
      memory-tag updates (rfe312-shift base 5))
     (rfe312-memory-read
      memory-tag updates (rfe312-shift base 6))
     (rfe312-memory-read
      memory-tag updates (rfe312-shift base 7))
     (rfe312-memory-read
      memory-tag updates (rfe312-shift base 8)))))

(defun rfe312-matrix-transpose (matrix)
  (rfe312-matrix
   (rfe312-matrix-entry matrix 0 0)
   (rfe312-matrix-entry matrix 1 0)
   (rfe312-matrix-entry matrix 2 0)
   (rfe312-matrix-entry matrix 0 1)
   (rfe312-matrix-entry matrix 1 1)
   (rfe312-matrix-entry matrix 2 1)
   (rfe312-matrix-entry matrix 0 2)
   (rfe312-matrix-entry matrix 1 2)
   (rfe312-matrix-entry matrix 2 2)))

(defun rfe312-dot3 (ctx a b c d e f)
  (rfe312-add
   ctx
   (rfe312-add
    ctx
    (rfe312-mul ctx a b)
    (rfe312-mul ctx c d))
   (rfe312-mul ctx e f)))

(defun rfe312-matrix-multiply (ctx left right)
  (rfe312-matrix
   (rfe312-dot3
    ctx
    (rfe312-matrix-entry left 0 0)
    (rfe312-matrix-entry right 0 0)
    (rfe312-matrix-entry left 0 1)
    (rfe312-matrix-entry right 1 0)
    (rfe312-matrix-entry left 0 2)
    (rfe312-matrix-entry right 2 0))
   (rfe312-dot3
    ctx
    (rfe312-matrix-entry left 0 0)
    (rfe312-matrix-entry right 0 1)
    (rfe312-matrix-entry left 0 1)
    (rfe312-matrix-entry right 1 1)
    (rfe312-matrix-entry left 0 2)
    (rfe312-matrix-entry right 2 1))
   (rfe312-dot3
    ctx
    (rfe312-matrix-entry left 0 0)
    (rfe312-matrix-entry right 0 2)
    (rfe312-matrix-entry left 0 1)
    (rfe312-matrix-entry right 1 2)
    (rfe312-matrix-entry left 0 2)
    (rfe312-matrix-entry right 2 2))
   (rfe312-dot3
    ctx
    (rfe312-matrix-entry left 1 0)
    (rfe312-matrix-entry right 0 0)
    (rfe312-matrix-entry left 1 1)
    (rfe312-matrix-entry right 1 0)
    (rfe312-matrix-entry left 1 2)
    (rfe312-matrix-entry right 2 0))
   (rfe312-dot3
    ctx
    (rfe312-matrix-entry left 1 0)
    (rfe312-matrix-entry right 0 1)
    (rfe312-matrix-entry left 1 1)
    (rfe312-matrix-entry right 1 1)
    (rfe312-matrix-entry left 1 2)
    (rfe312-matrix-entry right 2 1))
   (rfe312-dot3
    ctx
    (rfe312-matrix-entry left 1 0)
    (rfe312-matrix-entry right 0 2)
    (rfe312-matrix-entry left 1 1)
    (rfe312-matrix-entry right 1 2)
    (rfe312-matrix-entry left 1 2)
    (rfe312-matrix-entry right 2 2))
   (rfe312-dot3
    ctx
    (rfe312-matrix-entry left 2 0)
    (rfe312-matrix-entry right 0 0)
    (rfe312-matrix-entry left 2 1)
    (rfe312-matrix-entry right 1 0)
    (rfe312-matrix-entry left 2 2)
    (rfe312-matrix-entry right 2 0))
   (rfe312-dot3
    ctx
    (rfe312-matrix-entry left 2 0)
    (rfe312-matrix-entry right 0 1)
    (rfe312-matrix-entry left 2 1)
    (rfe312-matrix-entry right 1 1)
    (rfe312-matrix-entry left 2 2)
    (rfe312-matrix-entry right 2 1))
   (rfe312-dot3
    ctx
    (rfe312-matrix-entry left 2 0)
    (rfe312-matrix-entry right 0 2)
    (rfe312-matrix-entry left 2 1)
    (rfe312-matrix-entry right 1 2)
    (rfe312-matrix-entry left 2 2)
    (rfe312-matrix-entry right 2 2))))

(defun rfe312-matrix-equal-p (left right)
  (and
   (equal
    (rfe312-matrix-entry left 0 0)
    (rfe312-matrix-entry right 0 0))
   (equal
    (rfe312-matrix-entry left 0 1)
    (rfe312-matrix-entry right 0 1))
   (equal
    (rfe312-matrix-entry left 0 2)
    (rfe312-matrix-entry right 0 2))
   (equal
    (rfe312-matrix-entry left 1 0)
    (rfe312-matrix-entry right 1 0))
   (equal
    (rfe312-matrix-entry left 1 1)
    (rfe312-matrix-entry right 1 1))
   (equal
    (rfe312-matrix-entry left 1 2)
    (rfe312-matrix-entry right 1 2))
   (equal
    (rfe312-matrix-entry left 2 0)
    (rfe312-matrix-entry right 2 0))
   (equal
    (rfe312-matrix-entry left 2 1)
    (rfe312-matrix-entry right 2 1))
   (equal
    (rfe312-matrix-entry left 2 2)
    (rfe312-matrix-entry right 2 2))))

(defun rfe312-rotation-matrix-p (ctx zero one matrix)
  (rfe312-matrix-equal-p
   (rfe312-matrix-multiply
    ctx matrix (rfe312-matrix-transpose matrix))
   (rfe312-matrix
    one zero zero
    zero one zero
    zero zero one)))

(defun-sk
    ntp4vc-float-rmat-of-eulers-312-post-goal0-statement ()
  (forall
   (ctx zero one a-1 a memory-tag malloc-tag)
   (implies
    (and
     (rfe312-real-context-p ctx zero one)
     (rfe312-address-p a-1)
     (rfe312-address-p a)
     (rfe312-memory-function-p ctx memory-tag)
     (rfe312-malloc-function-p malloc-tag)
     (rfe312-region-function-p))
    (let*
        ((updates-0 nil)
         (r
          (rfe312-memory-read
           memory-tag updates-0 (rfe312-shift a-1 0)))
         (r-1 (rfe312-sin ctx r))
         (r-2
          (rfe312-memory-read
           memory-tag updates-0 (rfe312-shift a-1 2)))
         (r-3 (rfe312-sin ctx r-2))
         (r-4
          (rfe312-memory-read
           memory-tag updates-0 (rfe312-shift a-1 1)))
         (r-5 (rfe312-sin ctx r-4))
         (r-6 (rfe312-cos ctx r))
         (r-7 (rfe312-cos ctx r-2))
         (r-8 (rfe312-cos ctx r-4))
         (a-2 (rfe312-shift a 0))
         (r-9 (rfe312-mul ctx r-1 r-5))
         (r-10 (rfe312-neg ctx r-6))
         (r-11 (rfe312-mul ctx r-1 r-8))
         (updates-1
          (rfe312-memory-write
           updates-0
           (rfe312-shift a-2 0)
           (rfe312-add
            ctx
            (rfe312-mul ctx r-8 r-7)
            (rfe312-neg
             ctx
             (rfe312-mul ctx r-9 r-3)))))
         (updates-2
          (rfe312-memory-write
           updates-1
           (rfe312-shift a-2 1)
           (rfe312-add
            ctx
            (rfe312-mul ctx r-8 r-3)
            (rfe312-mul ctx r-9 r-7))))
         (updates-3
          (rfe312-memory-write
           updates-2
           (rfe312-shift a-2 2)
           (rfe312-mul ctx r-10 r-5)))
         (updates-4
          (rfe312-memory-write
           updates-3
           (rfe312-shift a-2 3)
           (rfe312-mul ctx r-10 r-3)))
         (updates-5
          (rfe312-memory-write
           updates-4
           (rfe312-shift a-2 4)
           (rfe312-mul ctx r-6 r-7)))
         (updates-6
          (rfe312-memory-write
           updates-5
           (rfe312-shift a-2 5)
           r-1))
         (updates-7
          (rfe312-memory-write
           updates-6
           (rfe312-shift a-2 6)
           (rfe312-add
            ctx
            (rfe312-mul ctx r-5 r-7)
            (rfe312-mul ctx r-11 r-3))))
         (updates-8
          (rfe312-memory-write
           updates-7
           (rfe312-shift a-2 7)
           (rfe312-add
            ctx
            (rfe312-mul ctx r-5 r-3)
            (rfe312-neg
             ctx
             (rfe312-mul ctx r-11 r-7)))))
         (updates-9
          (rfe312-memory-write
           updates-8
           (rfe312-shift a-2 8)
           (rfe312-mul ctx r-6 r-8))))
      (implies
       (and
        (<= (rfe312-region-op (rfe312-address-base a)) 0)
        (<= (rfe312-region-op (rfe312-address-base a-1)) 0)
        (rfe312-le ctx r-1 one)
        (rfe312-le ctx r-3 one)
        (rfe312-le ctx r-5 one)
        (rfe312-le ctx r-6 one)
        (rfe312-le ctx r-7 one)
        (rfe312-le ctx r-8 one)
        (rfe312-le ctx (rfe312-neg ctx one) r-1)
        (rfe312-le ctx (rfe312-neg ctx one) r-3)
        (rfe312-le ctx (rfe312-neg ctx one) r-5)
        (rfe312-le ctx (rfe312-neg ctx one) r-6)
        (rfe312-le ctx (rfe312-neg ctx one) r-7)
        (rfe312-le ctx (rfe312-neg ctx one) r-8)
        (rfe312-linked-p malloc-tag)
        (rfe312-valid-rw-p malloc-tag a 9)
        (rfe312-rvalid-floateulers-p
         malloc-tag memory-tag updates-0 a-1)
        (rfe312-is-finite32-p r)
        (rfe312-is-finite32-p r-2)
        (rfe312-is-finite32-p r-4)
        (rfe312-is-float32-p r)
        (rfe312-is-float32-p r-2)
        (rfe312-is-float32-p r-4)
        (rfe312-is-finite32-p r-1)
        (rfe312-is-finite32-p r-3)
        (rfe312-is-finite32-p r-5)
        (rfe312-is-finite32-p r-6)
        (rfe312-is-finite32-p r-7)
        (rfe312-is-finite32-p r-8)
        (rfe312-is-float32-p r-1)
        (rfe312-is-float32-p r-3)
        (rfe312-is-float32-p r-5)
        (rfe312-is-float32-p r-6)
        (rfe312-is-float32-p r-7)
        (rfe312-is-float32-p r-8))
       (rfe312-rotation-matrix-p
        ctx
        zero
        one
        (rfe312-matrix-of-memory
         memory-tag updates-9 a)))))))

(value-triple :itpeval-statement-checked)

:q
