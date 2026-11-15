;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/airborne/float_quat_of_rmat/float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_call_sqrtf_pre_arg_positive_3_goal6:
;; the generated rotation-matrix and memory conditions imply nonnegativity
;; of the square-root argument in the selected quaternion branch. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars are presented as an arbitrary real closed ordered field.  This
;; verification condition is first-order in field operations, order, memory,
;; and matrices.  Real closed fields are elementarily equivalent, so this
;; preserves its meaning over the mathematical reals without restricting
;; values to ACL2 rationals.  Each polynomial is represented directly by its
;; finite coefficient list in ascending degree order.

(defstub fqr-g6-real-op (ctx x) t)
(defstub fqr-g6-add-op (ctx x y) t)
(defstub fqr-g6-mul-op (ctx x y) t)
(defstub fqr-g6-neg-op (ctx x) t)
(defstub fqr-g6-inv-op (ctx x) t)
(defstub fqr-g6-lt-op (ctx x y) t)

(defun fqr-g6-real-p (ctx x)
  (if (fqr-g6-real-op ctx x) t nil))

(defun fqr-g6-add (ctx x y)
  (fqr-g6-add-op ctx x y))

(defun fqr-g6-mul (ctx x y)
  (fqr-g6-mul-op ctx x y))

(defun fqr-g6-neg (ctx x)
  (fqr-g6-neg-op ctx x))

(defun fqr-g6-inv (ctx x)
  (fqr-g6-inv-op ctx x))

(defun fqr-g6-sub (ctx x y)
  (fqr-g6-add ctx x (fqr-g6-neg ctx y)))

(defun fqr-g6-lt (ctx x y)
  (if (fqr-g6-lt-op ctx x y) t nil))

(defun fqr-g6-le (ctx x y)
  (not (fqr-g6-lt ctx y x)))

(defun-sk fqr-g6-field-laws-p (ctx zero one)
  (forall (x y z)
    (implies
     (and
      (fqr-g6-real-p ctx x)
      (fqr-g6-real-p ctx y)
      (fqr-g6-real-p ctx z))
     (and
      (fqr-g6-real-p ctx (fqr-g6-add ctx x y))
      (fqr-g6-real-p ctx (fqr-g6-mul ctx x y))
      (fqr-g6-real-p ctx (fqr-g6-neg ctx x))
      (fqr-g6-real-p ctx (fqr-g6-inv ctx x))
      (equal
       (fqr-g6-add ctx (fqr-g6-add ctx x y) z)
       (fqr-g6-add ctx x (fqr-g6-add ctx y z)))
      (equal
       (fqr-g6-add ctx x y)
       (fqr-g6-add ctx y x))
      (equal (fqr-g6-add ctx x zero) x)
      (equal
       (fqr-g6-add ctx x (fqr-g6-neg ctx x))
       zero)
      (equal
       (fqr-g6-mul ctx (fqr-g6-mul ctx x y) z)
       (fqr-g6-mul ctx x (fqr-g6-mul ctx y z)))
      (equal
       (fqr-g6-mul ctx x y)
       (fqr-g6-mul ctx y x))
      (equal (fqr-g6-mul ctx x one) x)
      (equal (fqr-g6-inv ctx zero) zero)
      (implies
       (not (equal x zero))
       (equal
        (fqr-g6-mul ctx x (fqr-g6-inv ctx x))
        one))
      (equal
       (fqr-g6-mul ctx x (fqr-g6-add ctx y z))
       (fqr-g6-add
        ctx
        (fqr-g6-mul ctx x y)
        (fqr-g6-mul ctx x z)))))))

(defun-sk fqr-g6-order-laws-p (ctx zero)
  (forall (x y z)
    (implies
     (and
      (fqr-g6-real-p ctx x)
      (fqr-g6-real-p ctx y)
      (fqr-g6-real-p ctx z))
     (and
      (not (fqr-g6-lt ctx x x))
      (or
       (equal x y)
       (fqr-g6-lt ctx x y)
       (fqr-g6-lt ctx y x))
      (implies
       (and
        (fqr-g6-lt ctx x y)
        (fqr-g6-lt ctx y z))
       (fqr-g6-lt ctx x z))
      (implies
       (fqr-g6-lt ctx x y)
       (fqr-g6-lt
        ctx
        (fqr-g6-add ctx x z)
        (fqr-g6-add ctx y z)))
      (implies
       (and
        (fqr-g6-lt ctx zero x)
        (fqr-g6-lt ctx zero y))
       (fqr-g6-lt
        ctx zero (fqr-g6-mul ctx x y)))))))

(defun-sk fqr-g6-positive-square-root-exists-p
    (ctx zero x)
  (exists (root)
    (and
     (fqr-g6-real-p ctx root)
     (fqr-g6-le ctx zero root)
     (equal (fqr-g6-mul ctx root root) x))))

(defun-sk fqr-g6-positive-square-root-laws-p (ctx zero)
  (forall (x)
    (implies
     (and
      (fqr-g6-real-p ctx x)
      (fqr-g6-lt ctx zero x))
     (fqr-g6-positive-square-root-exists-p
      ctx zero x))))

(defun fqr-g6-real-coefficient-list-p (ctx coefficients)
  (if (consp coefficients)
      (and
       (fqr-g6-real-p ctx (car coefficients))
       (fqr-g6-real-coefficient-list-p
        ctx (cdr coefficients)))
    (equal coefficients nil)))

(defun fqr-g6-poly-eval (ctx zero coefficients x)
  (if (consp coefficients)
    (fqr-g6-add
     ctx
     (car coefficients)
     (fqr-g6-mul
      ctx
      x
      (fqr-g6-poly-eval
       ctx zero (cdr coefficients) x)))
    zero))

(defun-sk fqr-g6-odd-polynomial-root-exists-p
    (ctx zero coefficients)
  (exists (root)
    (and
     (fqr-g6-real-p ctx root)
     (equal
      (fqr-g6-poly-eval
       ctx zero coefficients root)
      zero))))

(defun-sk fqr-g6-odd-root-laws-p (ctx zero)
  (forall (coefficients degree)
    (implies
     (and
      (natp degree)
      (not (equal degree 0))
      (oddp degree)
      (true-listp coefficients)
      (consp coefficients)
      (equal (len coefficients) (+ 1 degree))
      (fqr-g6-real-coefficient-list-p
       ctx coefficients)
      (not
       (equal
        (car (last coefficients))
        zero)))
     (fqr-g6-odd-polynomial-root-exists-p
      ctx zero coefficients))))

(defun fqr-g6-real-context-p (ctx zero one)
  (and
   (fqr-g6-real-p ctx zero)
   (fqr-g6-real-p ctx one)
   (not (equal zero one))
   (fqr-g6-lt ctx zero one)
   (fqr-g6-field-laws-p ctx zero one)
   (fqr-g6-order-laws-p ctx zero)
   (fqr-g6-positive-square-root-laws-p ctx zero)
   (fqr-g6-odd-root-laws-p ctx zero)))

;; Addresses are records with an integer base and integer offset.

(defun fqr-g6-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun fqr-g6-address-base (address)
  (car address))

(defun fqr-g6-address-offset (address)
  (cdr address))

(defun fqr-g6-shift (address amount)
  (cons
   (fqr-g6-address-base address)
   (+ (fqr-g6-address-offset address) amount)))

;; Tagged conservative interfaces retain the source's arbitrary functions.

(defstub fqr-g6-memory-at (memory-tag address) t)
(defstub fqr-g6-malloc-at (malloc-tag index) t)
(defstub fqr-g6-region-op (base) t)
(defstub fqr-g6-linked-op (malloc-tag) t)

(defun-sk fqr-g6-memory-function-p (ctx memory-tag)
  (forall (address)
    (implies
     (fqr-g6-address-p address)
     (fqr-g6-real-p
      ctx
      (fqr-g6-memory-at memory-tag address)))))

(defun-sk fqr-g6-malloc-function-p (malloc-tag)
  (forall (index)
    (implies
     (integerp index)
     (integerp
      (fqr-g6-malloc-at malloc-tag index)))))

(defun-sk fqr-g6-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (fqr-g6-region-op base)))))

(defun fqr-g6-linked-p (malloc-tag)
  (if (fqr-g6-linked-op malloc-tag) t nil))

(defun fqr-g6-valid-rw-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (< 0 (fqr-g6-address-base address))
    (<= 0 (fqr-g6-address-offset address))
    (<=
     (+ (fqr-g6-address-offset address) length)
     (fqr-g6-malloc-at
      malloc-tag
      (fqr-g6-address-base address))))))

(defun fqr-g6-valid-rd-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (fqr-g6-address-base address)))
    (<= 0 (fqr-g6-address-offset address))
    (<=
     (+ (fqr-g6-address-offset address) length)
     (fqr-g6-malloc-at
      malloc-tag
      (fqr-g6-address-base address))))))

(defun fqr-g6-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (fqr-g6-address-base left)
     (fqr-g6-address-base right)))
   (<=
    (+ (fqr-g6-address-offset right) right-length)
    (fqr-g6-address-offset left))
   (<=
    (+ (fqr-g6-address-offset left) left-length)
    (fqr-g6-address-offset right))))

;; IS_FLOAT32 is definitionally true in the shared source theory, and the
;; supplied classification axiom makes IS_FINITE32 true for every real.

(defun fqr-g6-is-float32-p (value)
  (declare (ignore value))
  t)

(defun fqr-g6-is-finite32-p (value)
  (declare (ignore value))
  t)

(defun fqr-g6-finite-floatrmat-p
    (memory-tag address)
  (let ((base (fqr-g6-shift address 0)))
    (and
     (fqr-g6-is-finite32-p
      (fqr-g6-memory-at
       memory-tag (fqr-g6-shift base 0)))
     (fqr-g6-is-finite32-p
      (fqr-g6-memory-at
       memory-tag (fqr-g6-shift base 1)))
     (fqr-g6-is-finite32-p
      (fqr-g6-memory-at
       memory-tag (fqr-g6-shift base 2)))
     (fqr-g6-is-finite32-p
      (fqr-g6-memory-at
       memory-tag (fqr-g6-shift base 3)))
     (fqr-g6-is-finite32-p
      (fqr-g6-memory-at
       memory-tag (fqr-g6-shift base 4)))
     (fqr-g6-is-finite32-p
      (fqr-g6-memory-at
       memory-tag (fqr-g6-shift base 5)))
     (fqr-g6-is-finite32-p
      (fqr-g6-memory-at
       memory-tag (fqr-g6-shift base 6)))
     (fqr-g6-is-finite32-p
      (fqr-g6-memory-at
       memory-tag (fqr-g6-shift base 7)))
     (fqr-g6-is-finite32-p
      (fqr-g6-memory-at
       memory-tag (fqr-g6-shift base 8))))))

(defun fqr-g6-rvalid-floatrmat-p
    (malloc-tag memory-tag address)
  (and
   (fqr-g6-finite-floatrmat-p memory-tag address)
   (fqr-g6-valid-rd-p malloc-tag address 9)))

;; Matrices are row-major nine-tuples, matching the source record.

(defun fqr-g6-matrix
    (a00 a01 a02 a10 a11 a12 a20 a21 a22)
  (list a00 a01 a02 a10 a11 a12 a20 a21 a22))

(defun fqr-g6-matrix-entry (matrix row column)
  (nth (+ (* 3 row) column) matrix))

(defun fqr-g6-matrix-of-memory (memory-tag address)
  (let ((base (fqr-g6-shift address 0)))
    (fqr-g6-matrix
     (fqr-g6-memory-at
      memory-tag (fqr-g6-shift base 0))
     (fqr-g6-memory-at
      memory-tag (fqr-g6-shift base 1))
     (fqr-g6-memory-at
      memory-tag (fqr-g6-shift base 2))
     (fqr-g6-memory-at
      memory-tag (fqr-g6-shift base 3))
     (fqr-g6-memory-at
      memory-tag (fqr-g6-shift base 4))
     (fqr-g6-memory-at
      memory-tag (fqr-g6-shift base 5))
     (fqr-g6-memory-at
      memory-tag (fqr-g6-shift base 6))
     (fqr-g6-memory-at
      memory-tag (fqr-g6-shift base 7))
     (fqr-g6-memory-at
      memory-tag (fqr-g6-shift base 8)))))

(defun fqr-g6-matrix-transpose (matrix)
  (fqr-g6-matrix
   (fqr-g6-matrix-entry matrix 0 0)
   (fqr-g6-matrix-entry matrix 1 0)
   (fqr-g6-matrix-entry matrix 2 0)
   (fqr-g6-matrix-entry matrix 0 1)
   (fqr-g6-matrix-entry matrix 1 1)
   (fqr-g6-matrix-entry matrix 2 1)
   (fqr-g6-matrix-entry matrix 0 2)
   (fqr-g6-matrix-entry matrix 1 2)
   (fqr-g6-matrix-entry matrix 2 2)))

(defun fqr-g6-dot3 (ctx a b c x y z)
  (fqr-g6-add
   ctx
   (fqr-g6-add
    ctx
    (fqr-g6-mul ctx a x)
    (fqr-g6-mul ctx b y))
   (fqr-g6-mul ctx c z)))

(defun fqr-g6-matrix-mul (ctx left right)
  (fqr-g6-matrix
   (fqr-g6-dot3
    ctx
    (fqr-g6-matrix-entry left 0 0)
    (fqr-g6-matrix-entry left 0 1)
    (fqr-g6-matrix-entry left 0 2)
    (fqr-g6-matrix-entry right 0 0)
    (fqr-g6-matrix-entry right 1 0)
    (fqr-g6-matrix-entry right 2 0))
   (fqr-g6-dot3
    ctx
    (fqr-g6-matrix-entry left 0 0)
    (fqr-g6-matrix-entry left 0 1)
    (fqr-g6-matrix-entry left 0 2)
    (fqr-g6-matrix-entry right 0 1)
    (fqr-g6-matrix-entry right 1 1)
    (fqr-g6-matrix-entry right 2 1))
   (fqr-g6-dot3
    ctx
    (fqr-g6-matrix-entry left 0 0)
    (fqr-g6-matrix-entry left 0 1)
    (fqr-g6-matrix-entry left 0 2)
    (fqr-g6-matrix-entry right 0 2)
    (fqr-g6-matrix-entry right 1 2)
    (fqr-g6-matrix-entry right 2 2))
   (fqr-g6-dot3
    ctx
    (fqr-g6-matrix-entry left 1 0)
    (fqr-g6-matrix-entry left 1 1)
    (fqr-g6-matrix-entry left 1 2)
    (fqr-g6-matrix-entry right 0 0)
    (fqr-g6-matrix-entry right 1 0)
    (fqr-g6-matrix-entry right 2 0))
   (fqr-g6-dot3
    ctx
    (fqr-g6-matrix-entry left 1 0)
    (fqr-g6-matrix-entry left 1 1)
    (fqr-g6-matrix-entry left 1 2)
    (fqr-g6-matrix-entry right 0 1)
    (fqr-g6-matrix-entry right 1 1)
    (fqr-g6-matrix-entry right 2 1))
   (fqr-g6-dot3
    ctx
    (fqr-g6-matrix-entry left 1 0)
    (fqr-g6-matrix-entry left 1 1)
    (fqr-g6-matrix-entry left 1 2)
    (fqr-g6-matrix-entry right 0 2)
    (fqr-g6-matrix-entry right 1 2)
    (fqr-g6-matrix-entry right 2 2))
   (fqr-g6-dot3
    ctx
    (fqr-g6-matrix-entry left 2 0)
    (fqr-g6-matrix-entry left 2 1)
    (fqr-g6-matrix-entry left 2 2)
    (fqr-g6-matrix-entry right 0 0)
    (fqr-g6-matrix-entry right 1 0)
    (fqr-g6-matrix-entry right 2 0))
   (fqr-g6-dot3
    ctx
    (fqr-g6-matrix-entry left 2 0)
    (fqr-g6-matrix-entry left 2 1)
    (fqr-g6-matrix-entry left 2 2)
    (fqr-g6-matrix-entry right 0 1)
    (fqr-g6-matrix-entry right 1 1)
    (fqr-g6-matrix-entry right 2 1))
   (fqr-g6-dot3
    ctx
    (fqr-g6-matrix-entry left 2 0)
    (fqr-g6-matrix-entry left 2 1)
    (fqr-g6-matrix-entry left 2 2)
    (fqr-g6-matrix-entry right 0 2)
    (fqr-g6-matrix-entry right 1 2)
    (fqr-g6-matrix-entry right 2 2))))

(defun fqr-g6-identity-matrix (zero one)
  (fqr-g6-matrix
   one zero zero
   zero one zero
   zero zero one))

(defun fqr-g6-rotation-matrix-p (ctx zero one matrix)
  (equal
   (fqr-g6-matrix-mul
    ctx matrix (fqr-g6-matrix-transpose matrix))
   (fqr-g6-identity-matrix zero one)))

(defun fqr-g6-determinant (ctx matrix)
  (let*
      ((a00 (fqr-g6-matrix-entry matrix 0 0))
       (a01 (fqr-g6-matrix-entry matrix 0 1))
       (a02 (fqr-g6-matrix-entry matrix 0 2))
       (a10 (fqr-g6-matrix-entry matrix 1 0))
       (a11 (fqr-g6-matrix-entry matrix 1 1))
       (a12 (fqr-g6-matrix-entry matrix 1 2))
       (a20 (fqr-g6-matrix-entry matrix 2 0))
       (a21 (fqr-g6-matrix-entry matrix 2 1))
       (a22 (fqr-g6-matrix-entry matrix 2 2)))
    (fqr-g6-sub
     ctx
     (fqr-g6-sub
      ctx
      (fqr-g6-sub
       ctx
       (fqr-g6-add
        ctx
        (fqr-g6-add
         ctx
         (fqr-g6-mul
          ctx (fqr-g6-mul ctx a00 a11) a22)
         (fqr-g6-mul
          ctx (fqr-g6-mul ctx a01 a12) a20))
        (fqr-g6-mul
         ctx (fqr-g6-mul ctx a02 a10) a21))
       (fqr-g6-mul
        ctx (fqr-g6-mul ctx a00 a12) a21))
      (fqr-g6-mul
       ctx (fqr-g6-mul ctx a01 a10) a22))
     (fqr-g6-mul
      ctx (fqr-g6-mul ctx a02 a11) a20))))

(defun fqr-g6-special-orthogonal-p (ctx one matrix)
  (equal (fqr-g6-determinant ctx matrix) one))

(defun-sk
    ntp4vc-float-quat-of-rmat-call-sqrtf-positive-3-goal6-statement
    ()
  (forall (ctx zero one a t-1 a-1 malloc-tag)
    (implies
     (and
      (fqr-g6-real-context-p ctx zero one)
      (fqr-g6-address-p a)
      (fqr-g6-address-p a-1)
      (fqr-g6-memory-function-p ctx t-1)
      (fqr-g6-malloc-function-p malloc-tag)
      (fqr-g6-region-function-p))
     (let*
         ((a-2 (fqr-g6-shift a 0))
          (r
           (fqr-g6-memory-at
            t-1 (fqr-g6-shift a-2 8)))
          (r-1
           (fqr-g6-memory-at
            t-1 (fqr-g6-shift a-2 4)))
          (r-2
           (fqr-g6-memory-at
            t-1 (fqr-g6-shift a-2 0)))
          (r-3
           (fqr-g6-add
            ctx (fqr-g6-add ctx r-2 r-1) r))
          (a-3 (fqr-g6-matrix-of-memory t-1 a)))
       (implies
        (and
         (<= (fqr-g6-region-op
              (fqr-g6-address-base a))
             0)
         (<= (fqr-g6-region-op
              (fqr-g6-address-base a-1))
             0)
         (fqr-g6-lt ctx r r-1)
         (fqr-g6-le ctx r-3 zero)
         (fqr-g6-linked-p malloc-tag)
         (fqr-g6-valid-rw-p malloc-tag a-1 4)
         (fqr-g6-rvalid-floatrmat-p
          malloc-tag t-1 a)
         (fqr-g6-separated-p a 9 a-1 4)
         (fqr-g6-rotation-matrix-p
          ctx zero one a-3)
         (fqr-g6-special-orthogonal-p
          ctx one a-3)
         (fqr-g6-is-float32-p r-2)
         (fqr-g6-is-float32-p
          (fqr-g6-memory-at
           t-1 (fqr-g6-shift a-2 2)))
         (fqr-g6-is-float32-p r-1)
         (fqr-g6-is-float32-p
          (fqr-g6-memory-at
           t-1 (fqr-g6-shift a-2 6)))
         (fqr-g6-is-float32-p r)
         (fqr-g6-is-float32-p r-3)
         (or
          (fqr-g6-le ctx r-2 r-1)
          (fqr-g6-le ctx r-2 r)))
        (fqr-g6-le
         ctx
         zero
         (fqr-g6-add
          ctx
          (fqr-g6-add
           ctx
           (fqr-g6-add
            ctx r-1 (fqr-g6-neg ctx r-2))
           (fqr-g6-neg ctx r))
          one)))))))

(value-triple :itpeval-statement-checked)

:q
