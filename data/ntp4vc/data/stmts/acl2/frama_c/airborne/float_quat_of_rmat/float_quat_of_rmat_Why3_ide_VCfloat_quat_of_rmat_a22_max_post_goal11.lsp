;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/airborne/float_quat_of_rmat/float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_a22_max_post_goal11:
;; the a22-max branch of a rotation-matrix-to-quaternion conversion returns
;; the specified real quaternion under the generated memory, branch, and
;; floating-value conditions. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars are presented as an arbitrary real closed ordered field.  The
;; source verification condition is first-order in field operations, order,
;; square root, addresses, and arbitrary tagged functions.  Real closed
;; fields are elementarily equivalent, so this preserves the statement over
;; the mathematical reals without restricting values to ACL2 rationals.

(defstub fqr-a22-real-op (ctx x) t)
(defstub fqr-a22-add-op (ctx x y) t)
(defstub fqr-a22-mul-op (ctx x y) t)
(defstub fqr-a22-neg-op (ctx x) t)
(defstub fqr-a22-inv-op (ctx x) t)
(defstub fqr-a22-lt-op (ctx x y) t)
(defstub fqr-a22-sqrt-op (ctx x) t)

(defun fqr-a22-real-p (ctx x)
  (if (fqr-a22-real-op ctx x) t nil))

(defun fqr-a22-add (ctx x y)
  (fqr-a22-add-op ctx x y))

(defun fqr-a22-mul (ctx x y)
  (fqr-a22-mul-op ctx x y))

(defun fqr-a22-neg (ctx x)
  (fqr-a22-neg-op ctx x))

(defun fqr-a22-inv (ctx x)
  (fqr-a22-inv-op ctx x))

(defun fqr-a22-sub (ctx x y)
  (fqr-a22-add ctx x (fqr-a22-neg ctx y)))

(defun fqr-a22-div (ctx x y)
  (fqr-a22-mul ctx x (fqr-a22-inv ctx y)))

(defun fqr-a22-lt (ctx x y)
  (if (fqr-a22-lt-op ctx x y) t nil))

(defun fqr-a22-le (ctx x y)
  (not (fqr-a22-lt ctx y x)))

(defun fqr-a22-sqrt (ctx x)
  (fqr-a22-sqrt-op ctx x))

(defun fqr-a22-two (ctx one)
  (fqr-a22-add ctx one one))

(defun fqr-a22-half (ctx one)
  (fqr-a22-div ctx one (fqr-a22-two ctx one)))

(defun fqr-a22-real-coefficient-list-p (ctx coefficients)
  (if (consp coefficients)
      (and
       (fqr-a22-real-p ctx (car coefficients))
       (fqr-a22-real-coefficient-list-p
        ctx (cdr coefficients)))
    (equal coefficients nil)))

;; Coefficients are listed in ascending degree order.  Directly quantifying
;; over these proper lists covers every finite polynomial coefficient tuple.

(defun fqr-a22-poly-eval
    (ctx zero coefficients x)
  (if (consp coefficients)
      (fqr-a22-add
       ctx
       (car coefficients)
       (fqr-a22-mul
        ctx
        x
        (fqr-a22-poly-eval
         ctx zero (cdr coefficients) x)))
    zero))

(defun fqr-a22-leading-coefficient (coefficients)
  (if (and
       (consp coefficients)
       (consp (cdr coefficients)))
      (fqr-a22-leading-coefficient (cdr coefficients))
    (car coefficients)))

(defun-sk fqr-a22-field-laws-p (ctx zero one)
  (forall (x y z)
    (implies
     (and
      (fqr-a22-real-p ctx x)
      (fqr-a22-real-p ctx y)
      (fqr-a22-real-p ctx z))
     (and
      (fqr-a22-real-p ctx (fqr-a22-add ctx x y))
      (fqr-a22-real-p ctx (fqr-a22-mul ctx x y))
      (fqr-a22-real-p ctx (fqr-a22-neg ctx x))
      (fqr-a22-real-p ctx (fqr-a22-inv ctx x))
      (equal
       (fqr-a22-add ctx (fqr-a22-add ctx x y) z)
       (fqr-a22-add ctx x (fqr-a22-add ctx y z)))
      (equal
       (fqr-a22-add ctx x y)
       (fqr-a22-add ctx y x))
      (equal (fqr-a22-add ctx x zero) x)
      (equal
       (fqr-a22-add ctx x (fqr-a22-neg ctx x))
       zero)
      (equal
       (fqr-a22-mul ctx (fqr-a22-mul ctx x y) z)
       (fqr-a22-mul ctx x (fqr-a22-mul ctx y z)))
      (equal
       (fqr-a22-mul ctx x y)
       (fqr-a22-mul ctx y x))
      (equal (fqr-a22-mul ctx x one) x)
      (equal (fqr-a22-inv ctx zero) zero)
      (implies
       (not (equal x zero))
       (equal
        (fqr-a22-mul ctx x (fqr-a22-inv ctx x))
        one))
      (equal
       (fqr-a22-mul ctx x (fqr-a22-add ctx y z))
       (fqr-a22-add
        ctx
        (fqr-a22-mul ctx x y)
        (fqr-a22-mul ctx x z)))))))

(defun-sk fqr-a22-order-laws-p (ctx zero)
  (forall (x y z)
    (implies
     (and
      (fqr-a22-real-p ctx x)
      (fqr-a22-real-p ctx y)
      (fqr-a22-real-p ctx z))
     (and
      (not (fqr-a22-lt ctx x x))
      (or
       (equal x y)
       (fqr-a22-lt ctx x y)
       (fqr-a22-lt ctx y x))
      (implies
       (and
        (fqr-a22-lt ctx x y)
        (fqr-a22-lt ctx y z))
       (fqr-a22-lt ctx x z))
      (implies
       (fqr-a22-lt ctx x y)
       (fqr-a22-lt
        ctx
        (fqr-a22-add ctx x z)
        (fqr-a22-add ctx y z)))
      (implies
       (and
        (fqr-a22-lt ctx zero x)
        (fqr-a22-lt ctx zero y))
       (fqr-a22-lt
        ctx zero (fqr-a22-mul ctx x y)))))))

(defun-sk fqr-a22-sqrt-laws-p (ctx zero)
  (forall (x)
    (implies
     (fqr-a22-real-p ctx x)
     (and
      (fqr-a22-real-p ctx (fqr-a22-sqrt ctx x))
      (if (fqr-a22-lt ctx x zero)
          (equal (fqr-a22-sqrt ctx x) zero)
        (and
         (fqr-a22-le ctx zero (fqr-a22-sqrt ctx x))
         (equal
          (fqr-a22-mul
           ctx
           (fqr-a22-sqrt ctx x)
           (fqr-a22-sqrt ctx x))
          x)))))))

(defun-sk fqr-a22-odd-polynomial-root-exists-p
    (ctx zero coefficients)
  (exists (root)
    (and
     (fqr-a22-real-p ctx root)
     (equal
      (fqr-a22-poly-eval
       ctx zero coefficients root)
      zero))))

(defun-sk fqr-a22-odd-root-laws-p (ctx zero)
  (forall (coefficients)
    (implies
     (and
      (consp coefficients)
      (fqr-a22-real-coefficient-list-p
       ctx coefficients)
      (oddp (1- (len coefficients)))
      (not
       (equal
        (fqr-a22-leading-coefficient coefficients)
        zero)))
     (fqr-a22-odd-polynomial-root-exists-p
      ctx zero coefficients))))

(defun fqr-a22-real-context-p (ctx zero one)
  (and
   (fqr-a22-real-p ctx zero)
   (fqr-a22-real-p ctx one)
   (not (equal zero one))
   (fqr-a22-lt ctx zero one)
   (fqr-a22-field-laws-p ctx zero one)
   (fqr-a22-order-laws-p ctx zero)
   (fqr-a22-sqrt-laws-p ctx zero)
   (fqr-a22-odd-root-laws-p ctx zero)))

;; Addresses are the source record of an integer base and integer offset.

(defun fqr-a22-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun fqr-a22-address-base (address)
  (car address))

(defun fqr-a22-address-offset (address)
  (cdr address))

(defun fqr-a22-shift (address amount)
  (cons
   (fqr-a22-address-base address)
   (+ (fqr-a22-address-offset address) amount)))

;; Tagged conservative interfaces retain the source's arbitrary functions.

(defstub fqr-a22-memory-at (memory-tag address) t)
(defstub fqr-a22-malloc-at (malloc-tag index) t)
(defstub fqr-a22-region-op (base) t)
(defstub fqr-a22-linked-op (malloc-tag) t)

(defun-sk fqr-a22-memory-function-p (ctx memory-tag)
  (forall (address)
    (implies
     (fqr-a22-address-p address)
     (fqr-a22-real-p
      ctx
      (fqr-a22-memory-at memory-tag address)))))

(defun-sk fqr-a22-malloc-function-p (malloc-tag)
  (forall (index)
    (implies
     (integerp index)
     (integerp
      (fqr-a22-malloc-at malloc-tag index)))))

(defun-sk fqr-a22-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (fqr-a22-region-op base)))))

(defun fqr-a22-linked-p (malloc-tag)
  (if (fqr-a22-linked-op malloc-tag) t nil))

(defun fqr-a22-memory-read (memory-tag updates address)
  (let ((entry (assoc-equal address updates)))
    (if entry
        (cdr entry)
      (fqr-a22-memory-at memory-tag address))))

(defun fqr-a22-memory-write (updates address value)
  (cons (cons address value) updates))

(defun-sk fqr-a22-memory-equal-p
    (left-tag left-updates right-tag right-updates)
  (forall (address)
    (implies
     (fqr-a22-address-p address)
     (equal
      (fqr-a22-memory-read
       left-tag left-updates address)
      (fqr-a22-memory-read
       right-tag right-updates address)))))

(defun fqr-a22-valid-rw-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (< 0 (fqr-a22-address-base address))
    (<= 0 (fqr-a22-address-offset address))
    (<=
     (+ (fqr-a22-address-offset address) length)
     (fqr-a22-malloc-at
      malloc-tag
      (fqr-a22-address-base address))))))

(defun fqr-a22-valid-rd-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (fqr-a22-address-base address)))
    (<= 0 (fqr-a22-address-offset address))
    (<=
     (+ (fqr-a22-address-offset address) length)
     (fqr-a22-malloc-at
      malloc-tag
      (fqr-a22-address-base address))))))

(defun fqr-a22-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (fqr-a22-address-base left)
     (fqr-a22-address-base right)))
   (<=
    (+ (fqr-a22-address-offset right) right-length)
    (fqr-a22-address-offset left))
   (<=
    (+ (fqr-a22-address-offset left) left-length)
    (fqr-a22-address-offset right))))

;; In the shared source theory IS_FLOAT32 is definitionally true, while the
;; supplied classification axiom makes IS_FINITE32 true for every real.

(defun fqr-a22-is-float32-p (value)
  (declare (ignore value))
  t)

(defun fqr-a22-is-finite32-p (value)
  (declare (ignore value))
  t)

(defun fqr-a22-finite-floatrmat-p
    (memory-tag updates address)
  (and
   (fqr-a22-is-finite32-p
    (fqr-a22-memory-read
     memory-tag updates (fqr-a22-shift address 0)))
   (fqr-a22-is-finite32-p
    (fqr-a22-memory-read
     memory-tag updates (fqr-a22-shift address 1)))
   (fqr-a22-is-finite32-p
    (fqr-a22-memory-read
     memory-tag updates (fqr-a22-shift address 2)))
   (fqr-a22-is-finite32-p
    (fqr-a22-memory-read
     memory-tag updates (fqr-a22-shift address 3)))
   (fqr-a22-is-finite32-p
    (fqr-a22-memory-read
     memory-tag updates (fqr-a22-shift address 4)))
   (fqr-a22-is-finite32-p
    (fqr-a22-memory-read
     memory-tag updates (fqr-a22-shift address 5)))
   (fqr-a22-is-finite32-p
    (fqr-a22-memory-read
     memory-tag updates (fqr-a22-shift address 6)))
   (fqr-a22-is-finite32-p
    (fqr-a22-memory-read
     memory-tag updates (fqr-a22-shift address 7)))
   (fqr-a22-is-finite32-p
    (fqr-a22-memory-read
     memory-tag updates (fqr-a22-shift address 8)))))

(defun fqr-a22-rvalid-floatrmat-p
    (malloc-tag memory-tag updates address)
  (and
   (fqr-a22-finite-floatrmat-p
    memory-tag updates address)
   (fqr-a22-valid-rd-p malloc-tag address 9)))

;; Matrices use row-major nine-tuples and quaternions use scalar/x/y/z
;; four-tuples, exactly matching the source records.

(defun fqr-a22-matrix
    (a00 a01 a02 a10 a11 a12 a20 a21 a22)
  (list a00 a01 a02 a10 a11 a12 a20 a21 a22))

(defun fqr-a22-matrix-entry (matrix row column)
  (nth (+ (* 3 row) column) matrix))

(defun fqr-a22-matrix-of-memory
    (memory-tag updates address)
  (fqr-a22-matrix
   (fqr-a22-memory-read
    memory-tag updates (fqr-a22-shift address 0))
   (fqr-a22-memory-read
    memory-tag updates (fqr-a22-shift address 1))
   (fqr-a22-memory-read
    memory-tag updates (fqr-a22-shift address 2))
   (fqr-a22-memory-read
    memory-tag updates (fqr-a22-shift address 3))
   (fqr-a22-memory-read
    memory-tag updates (fqr-a22-shift address 4))
   (fqr-a22-memory-read
    memory-tag updates (fqr-a22-shift address 5))
   (fqr-a22-memory-read
    memory-tag updates (fqr-a22-shift address 6))
   (fqr-a22-memory-read
    memory-tag updates (fqr-a22-shift address 7))
   (fqr-a22-memory-read
    memory-tag updates (fqr-a22-shift address 8))))

(defun fqr-a22-matrix-transpose (matrix)
  (fqr-a22-matrix
   (fqr-a22-matrix-entry matrix 0 0)
   (fqr-a22-matrix-entry matrix 1 0)
   (fqr-a22-matrix-entry matrix 2 0)
   (fqr-a22-matrix-entry matrix 0 1)
   (fqr-a22-matrix-entry matrix 1 1)
   (fqr-a22-matrix-entry matrix 2 1)
   (fqr-a22-matrix-entry matrix 0 2)
   (fqr-a22-matrix-entry matrix 1 2)
   (fqr-a22-matrix-entry matrix 2 2)))

(defun fqr-a22-dot3 (ctx a b c x y z)
  (fqr-a22-add
   ctx
   (fqr-a22-add
    ctx
    (fqr-a22-mul ctx a x)
    (fqr-a22-mul ctx b y))
   (fqr-a22-mul ctx c z)))

(defun fqr-a22-matrix-mul (ctx left right)
  (fqr-a22-matrix
   (fqr-a22-dot3
    ctx
    (fqr-a22-matrix-entry left 0 0)
    (fqr-a22-matrix-entry left 0 1)
    (fqr-a22-matrix-entry left 0 2)
    (fqr-a22-matrix-entry right 0 0)
    (fqr-a22-matrix-entry right 1 0)
    (fqr-a22-matrix-entry right 2 0))
   (fqr-a22-dot3
    ctx
    (fqr-a22-matrix-entry left 0 0)
    (fqr-a22-matrix-entry left 0 1)
    (fqr-a22-matrix-entry left 0 2)
    (fqr-a22-matrix-entry right 0 1)
    (fqr-a22-matrix-entry right 1 1)
    (fqr-a22-matrix-entry right 2 1))
   (fqr-a22-dot3
    ctx
    (fqr-a22-matrix-entry left 0 0)
    (fqr-a22-matrix-entry left 0 1)
    (fqr-a22-matrix-entry left 0 2)
    (fqr-a22-matrix-entry right 0 2)
    (fqr-a22-matrix-entry right 1 2)
    (fqr-a22-matrix-entry right 2 2))
   (fqr-a22-dot3
    ctx
    (fqr-a22-matrix-entry left 1 0)
    (fqr-a22-matrix-entry left 1 1)
    (fqr-a22-matrix-entry left 1 2)
    (fqr-a22-matrix-entry right 0 0)
    (fqr-a22-matrix-entry right 1 0)
    (fqr-a22-matrix-entry right 2 0))
   (fqr-a22-dot3
    ctx
    (fqr-a22-matrix-entry left 1 0)
    (fqr-a22-matrix-entry left 1 1)
    (fqr-a22-matrix-entry left 1 2)
    (fqr-a22-matrix-entry right 0 1)
    (fqr-a22-matrix-entry right 1 1)
    (fqr-a22-matrix-entry right 2 1))
   (fqr-a22-dot3
    ctx
    (fqr-a22-matrix-entry left 1 0)
    (fqr-a22-matrix-entry left 1 1)
    (fqr-a22-matrix-entry left 1 2)
    (fqr-a22-matrix-entry right 0 2)
    (fqr-a22-matrix-entry right 1 2)
    (fqr-a22-matrix-entry right 2 2))
   (fqr-a22-dot3
    ctx
    (fqr-a22-matrix-entry left 2 0)
    (fqr-a22-matrix-entry left 2 1)
    (fqr-a22-matrix-entry left 2 2)
    (fqr-a22-matrix-entry right 0 0)
    (fqr-a22-matrix-entry right 1 0)
    (fqr-a22-matrix-entry right 2 0))
   (fqr-a22-dot3
    ctx
    (fqr-a22-matrix-entry left 2 0)
    (fqr-a22-matrix-entry left 2 1)
    (fqr-a22-matrix-entry left 2 2)
    (fqr-a22-matrix-entry right 0 1)
    (fqr-a22-matrix-entry right 1 1)
    (fqr-a22-matrix-entry right 2 1))
   (fqr-a22-dot3
    ctx
    (fqr-a22-matrix-entry left 2 0)
    (fqr-a22-matrix-entry left 2 1)
    (fqr-a22-matrix-entry left 2 2)
    (fqr-a22-matrix-entry right 0 2)
    (fqr-a22-matrix-entry right 1 2)
    (fqr-a22-matrix-entry right 2 2))))

(defun fqr-a22-identity-matrix (zero one)
  (fqr-a22-matrix
   one zero zero
   zero one zero
   zero zero one))

(defun fqr-a22-rotation-matrix-p (ctx zero one matrix)
  (equal
   (fqr-a22-matrix-mul
    ctx matrix (fqr-a22-matrix-transpose matrix))
   (fqr-a22-identity-matrix zero one)))

(defun fqr-a22-determinant (ctx matrix)
  (let*
      ((a00 (fqr-a22-matrix-entry matrix 0 0))
       (a01 (fqr-a22-matrix-entry matrix 0 1))
       (a02 (fqr-a22-matrix-entry matrix 0 2))
       (a10 (fqr-a22-matrix-entry matrix 1 0))
       (a11 (fqr-a22-matrix-entry matrix 1 1))
       (a12 (fqr-a22-matrix-entry matrix 1 2))
       (a20 (fqr-a22-matrix-entry matrix 2 0))
       (a21 (fqr-a22-matrix-entry matrix 2 1))
       (a22 (fqr-a22-matrix-entry matrix 2 2)))
    (fqr-a22-sub
     ctx
     (fqr-a22-sub
      ctx
      (fqr-a22-sub
       ctx
       (fqr-a22-add
        ctx
        (fqr-a22-add
         ctx
         (fqr-a22-mul
          ctx (fqr-a22-mul ctx a00 a11) a22)
         (fqr-a22-mul
          ctx (fqr-a22-mul ctx a01 a12) a20))
        (fqr-a22-mul
         ctx (fqr-a22-mul ctx a02 a10) a21))
       (fqr-a22-mul
        ctx (fqr-a22-mul ctx a00 a12) a21))
      (fqr-a22-mul
       ctx (fqr-a22-mul ctx a01 a10) a22))
     (fqr-a22-mul
      ctx (fqr-a22-mul ctx a02 a11) a20))))

(defun fqr-a22-special-orthogonal-p (ctx one matrix)
  (equal (fqr-a22-determinant ctx matrix) one))

(defun fqr-a22-trace (ctx matrix)
  (fqr-a22-add
   ctx
   (fqr-a22-add
    ctx
    (fqr-a22-matrix-entry matrix 0 0)
    (fqr-a22-matrix-entry matrix 1 1))
   (fqr-a22-matrix-entry matrix 2 2)))

(defun fqr-a22-quaternion (qi qx qy qz)
  (list qi qx qy qz))

(defun fqr-a22-quaternion-of-memory
    (memory-tag updates address)
  (fqr-a22-quaternion
   (fqr-a22-memory-read
    memory-tag updates (fqr-a22-shift address 0))
   (fqr-a22-memory-read
    memory-tag updates (fqr-a22-shift address 1))
   (fqr-a22-memory-read
    memory-tag updates (fqr-a22-shift address 2))
   (fqr-a22-memory-read
    memory-tag updates (fqr-a22-shift address 3))))

(defun fqr-a22-max2-quaternion (ctx one matrix)
  (let*
      ((a00 (fqr-a22-matrix-entry matrix 0 0))
       (a01 (fqr-a22-matrix-entry matrix 0 1))
       (a02 (fqr-a22-matrix-entry matrix 0 2))
       (a10 (fqr-a22-matrix-entry matrix 1 0))
       (a11 (fqr-a22-matrix-entry matrix 1 1))
       (a12 (fqr-a22-matrix-entry matrix 1 2))
       (a20 (fqr-a22-matrix-entry matrix 2 0))
       (a21 (fqr-a22-matrix-entry matrix 2 1))
       (a22 (fqr-a22-matrix-entry matrix 2 2))
       (root
        (fqr-a22-sqrt
         ctx
         (fqr-a22-sub
          ctx
          (fqr-a22-sub
           ctx
           (fqr-a22-add ctx one a22)
           a00)
          a11)))
       (twice-root
        (fqr-a22-mul ctx (fqr-a22-two ctx one) root)))
    (fqr-a22-quaternion
     (fqr-a22-div
      ctx (fqr-a22-sub ctx a10 a01) twice-root)
     (fqr-a22-div
      ctx (fqr-a22-add ctx a02 a20) twice-root)
     (fqr-a22-div
      ctx (fqr-a22-add ctx a12 a21) twice-root)
     (fqr-a22-mul ctx (fqr-a22-half ctx one) root))))

(defun fqr-a22-max2-transposed-memory-quaternion
    (ctx one memory-tag address)
  (fqr-a22-max2-quaternion
   ctx
   one
   (fqr-a22-matrix-transpose
    (fqr-a22-matrix-of-memory
     memory-tag nil address))))

(defun
    ntp4vc-float-quat-of-rmat-a22-max-post-goal11-statement
    (ctx zero one
         a t-1 a-1 t-8 r-3 r-7 t-7 r-6 r-2 t-4 r-1
         t-6 r-5 r t-5 r-4 malloc-tag t-9 t-2 t-3)
   (implies
    (and
     (fqr-a22-real-context-p ctx zero one)
     (fqr-a22-address-p a)
     (fqr-a22-address-p a-1)
     (fqr-a22-memory-function-p ctx t-1)
     (fqr-a22-memory-function-p ctx t-8)
     (fqr-a22-memory-function-p ctx t-7)
     (fqr-a22-memory-function-p ctx t-4)
     (fqr-a22-memory-function-p ctx t-6)
     (fqr-a22-memory-function-p ctx t-5)
     (fqr-a22-memory-function-p ctx t-9)
     (fqr-a22-memory-function-p ctx t-2)
     (fqr-a22-memory-function-p ctx t-3)
     (fqr-a22-malloc-function-p malloc-tag)
     (fqr-a22-region-function-p)
     (fqr-a22-real-p ctx r-3)
     (fqr-a22-real-p ctx r-7)
     (fqr-a22-real-p ctx r-6)
     (fqr-a22-real-p ctx r-2)
     (fqr-a22-real-p ctx r-1)
     (fqr-a22-real-p ctx r-5)
     (fqr-a22-real-p ctx r)
     (fqr-a22-real-p ctx r-4))
    (let*
        ((a-2 (fqr-a22-shift a 0))
         (a-3 (fqr-a22-shift a-2 0))
         (r-8 (fqr-a22-memory-read t-1 nil a-3))
         (a-4 (fqr-a22-shift a-2 8))
         (r-9 (fqr-a22-memory-read t-1 nil a-4))
         (a-5 (fqr-a22-shift a-2 4))
         (r-10 (fqr-a22-memory-read t-1 nil a-5))
         (matrix-6
          (fqr-a22-matrix-of-memory t-1 nil a))
         (r-11
          (fqr-a22-add
           ctx
           (fqr-a22-add ctx r-8 r-10)
           r-9))
         (a-7 (fqr-a22-shift a-1 0))
         (m
          (fqr-a22-memory-write
           nil
           a-7
           (fqr-a22-mul
            ctx (fqr-a22-half ctx one) r-3)))
         (a-8 (fqr-a22-shift a-1 1))
         (a-9 (fqr-a22-shift a-2 5))
         (a-10 (fqr-a22-shift a-2 7))
         (m-1
          (fqr-a22-memory-write
           m
           a-8
           (fqr-a22-div
            ctx
            (fqr-a22-sub
             ctx
             (fqr-a22-memory-read t-8 m a-9)
             (fqr-a22-memory-read t-8 m a-10))
            r-7)))
         (a-11 (fqr-a22-shift a-1 2))
         (a-12 (fqr-a22-shift a-2 6))
         (a-13 (fqr-a22-shift a-2 2))
         (m-2
          (fqr-a22-memory-write
           m-1
           a-11
           (fqr-a22-div
            ctx
            (fqr-a22-sub
             ctx
             (fqr-a22-memory-read t-8 m-1 a-12)
             (fqr-a22-memory-read t-8 m-1 a-13))
            r-7)))
         (a-14 (fqr-a22-shift a-1 3))
         (a-15 (fqr-a22-shift a-2 1))
         (a-16 (fqr-a22-shift a-2 3))
         (r-13
          (fqr-a22-add
           ctx
           one
           (fqr-a22-add
            ctx
            (fqr-a22-add
             ctx
             (fqr-a22-memory-read t-8 nil a-3)
             (fqr-a22-memory-read t-8 nil a-5))
            (fqr-a22-memory-read t-8 nil a-4))))
         (m-3a
          (fqr-a22-memory-write
           nil
           a-7
           (fqr-a22-div
            ctx
            (fqr-a22-sub
             ctx
             (fqr-a22-memory-read t-7 nil a-9)
             (fqr-a22-memory-read t-7 nil a-10))
            r-6)))
         (m-3
          (fqr-a22-memory-write
           m-3a
           a-8
           (fqr-a22-mul
            ctx (fqr-a22-half ctx one) r-2)))
         (m-4
          (fqr-a22-memory-write
           m-3
           a-11
           (fqr-a22-div
            ctx
            (fqr-a22-add
             ctx
             (fqr-a22-memory-read t-7 m-3 a-15)
             (fqr-a22-memory-read t-7 m-3 a-16))
            r-6)))
         (r-15
          (fqr-a22-add
           ctx
           (fqr-a22-sub
            ctx
            (fqr-a22-sub
             ctx
             (fqr-a22-memory-read t-7 nil a-3)
             (fqr-a22-memory-read t-7 nil a-5))
            (fqr-a22-memory-read t-7 nil a-4))
           one))
         (r-16 (fqr-a22-memory-read t-4 nil a-4))
         (r-17 (fqr-a22-memory-read t-4 nil a-5))
         (r-19
          (fqr-a22-mul ctx (fqr-a22-two ctx one) r-1))
         (m-5
          (fqr-a22-memory-write
           nil
           a-7
           (fqr-a22-div
            ctx
            (fqr-a22-sub
             ctx
             (fqr-a22-memory-read t-6 nil a-12)
             (fqr-a22-memory-read t-6 nil a-13))
            r-5)))
         (m-6a
          (fqr-a22-memory-write
           m-5
           a-8
           (fqr-a22-div
            ctx
            (fqr-a22-add
             ctx
             (fqr-a22-memory-read t-6 m-5 a-15)
             (fqr-a22-memory-read t-6 m-5 a-16))
            r-5)))
         (m-6
          (fqr-a22-memory-write
           m-6a
           a-11
           (fqr-a22-mul
            ctx (fqr-a22-half ctx one) r-1)))
         (m-7
          (fqr-a22-memory-write
           m-6
           a-14
           (fqr-a22-div
            ctx
            (fqr-a22-add
             ctx
             (fqr-a22-memory-read t-6 m-6 a-9)
             (fqr-a22-memory-read t-6 m-6 a-10))
            r-5)))
         (r-20
          (fqr-a22-add
           ctx
           (fqr-a22-sub
            ctx
            (fqr-a22-sub
             ctx
             (fqr-a22-memory-read t-6 nil a-5)
             (fqr-a22-memory-read t-6 nil a-3))
            (fqr-a22-memory-read t-6 nil a-4))
           one))
         (r-22
          (fqr-a22-mul ctx (fqr-a22-two ctx one) r))
         (m-8
          (fqr-a22-memory-write
           nil
           a-7
           (fqr-a22-div
            ctx
            (fqr-a22-sub
             ctx
             (fqr-a22-memory-read t-5 nil a-15)
             (fqr-a22-memory-read t-5 nil a-16))
            r-4)))
         (m-9
          (fqr-a22-memory-write
           m-8
           a-8
           (fqr-a22-div
            ctx
            (fqr-a22-add
             ctx
             (fqr-a22-memory-read t-5 m-8 a-12)
             (fqr-a22-memory-read t-5 m-8 a-13))
            r-4)))
         (m-10a
          (fqr-a22-memory-write
           m-9
           a-11
           (fqr-a22-div
            ctx
            (fqr-a22-add
             ctx
             (fqr-a22-memory-read t-5 m-9 a-9)
             (fqr-a22-memory-read t-5 m-9 a-10))
            r-4)))
         (m-10
          (fqr-a22-memory-write
           m-10a
           a-14
           (fqr-a22-mul
            ctx (fqr-a22-half ctx one) r)))
         (r-23
          (fqr-a22-add
           ctx
           (fqr-a22-sub
            ctx
            (fqr-a22-sub
             ctx
             (fqr-a22-memory-read t-5 nil a-4)
             (fqr-a22-memory-read t-5 nil a-3))
            (fqr-a22-memory-read t-5 nil a-5))
           one))
         (m-2-final
          (fqr-a22-memory-write
           m-2
           a-14
           (fqr-a22-div
            ctx
            (fqr-a22-sub
             ctx
             (fqr-a22-memory-read t-8 m-2 a-15)
             (fqr-a22-memory-read t-8 m-2 a-16))
            r-7)))
         (m-4-final
          (fqr-a22-memory-write
           m-4
           a-14
           (fqr-a22-div
            ctx
            (fqr-a22-add
             ctx
             (fqr-a22-memory-read t-7 m-4 a-12)
             (fqr-a22-memory-read t-7 m-4 a-13))
            r-6))))
      (implies
       (and
        (fqr-a22-le
         ctx (fqr-a22-trace ctx matrix-6) zero)
        (<= (fqr-a22-region-op
             (fqr-a22-address-base a))
            0)
        (<= (fqr-a22-region-op
             (fqr-a22-address-base a-1))
            0)
        (fqr-a22-le ctx r-8 r-9)
        (fqr-a22-le ctx r-10 r-9)
        (fqr-a22-linked-p malloc-tag)
        (fqr-a22-is-float32-p r)
        (fqr-a22-is-float32-p r-1)
        (fqr-a22-is-float32-p r-2)
        (fqr-a22-is-float32-p r-3)
        (fqr-a22-is-float32-p r-4)
        (fqr-a22-is-float32-p r-5)
        (fqr-a22-is-float32-p r-6)
        (fqr-a22-is-float32-p r-7)
        (fqr-a22-valid-rw-p malloc-tag a-1 4)
        (fqr-a22-rvalid-floatrmat-p
         malloc-tag t-1 nil a)
        (fqr-a22-separated-p a 9 a-1 4)
        (fqr-a22-rotation-matrix-p
         ctx zero one matrix-6)
        (fqr-a22-special-orthogonal-p
         ctx one matrix-6)
        (fqr-a22-is-float32-p r-8)
        (fqr-a22-is-float32-p r-10)
        (fqr-a22-is-float32-p r-9)
        (fqr-a22-is-float32-p r-11)
        (if (fqr-a22-lt ctx zero r-11)
            (and
             (fqr-a22-memory-equal-p
              t-8 nil t-1 nil)
             (equal
              (fqr-a22-mul
               ctx (fqr-a22-two ctx one) r-3)
              r-7)
             (fqr-a22-memory-equal-p
              t-8 m-2-final t-9 nil)
             (fqr-a22-le ctx zero r-3)
             (fqr-a22-le ctx zero r-13)
             (fqr-a22-is-finite32-p r-3)
             (fqr-a22-is-finite32-p r-13))
          (and
           (fqr-a22-memory-equal-p
            t-2 nil t-1 nil)
           (if
               (fqr-a22-lt
                ctx
                (fqr-a22-memory-read t-2 nil a-5)
                (fqr-a22-memory-read t-2 nil a-3))
               (and
                (fqr-a22-memory-equal-p
                 t-3 nil t-2 nil)
                (if
                    (fqr-a22-lt
                     ctx
                     (fqr-a22-memory-read t-3 nil a-4)
                     (fqr-a22-memory-read t-3 nil a-3))
                    (and
                     (fqr-a22-memory-equal-p
                      t-7 nil t-3 nil)
                     (equal
                      (fqr-a22-mul
                       ctx
                       (fqr-a22-two ctx one)
                       r-2)
                      r-6)
                     (fqr-a22-memory-equal-p
                      t-7 m-4-final t-9 nil)
                     (fqr-a22-le ctx zero r-2)
                     (fqr-a22-le ctx zero r-15)
                     (fqr-a22-is-finite32-p r-2)
                     (fqr-a22-is-finite32-p r-15))
                  (and
                   (fqr-a22-memory-equal-p
                    t-4 nil t-3 nil)
                   (if (fqr-a22-lt ctx r-16 r-17)
                       (and
                        (fqr-a22-memory-equal-p
                         t-6 nil t-4 nil)
                        (equal r-19 r-5)
                        (fqr-a22-memory-equal-p
                         t-6 m-7 t-9 nil)
                        (fqr-a22-le ctx zero r-1)
                        (fqr-a22-le ctx zero r-20)
                        (fqr-a22-is-finite32-p r-1)
                        (fqr-a22-is-finite32-p r-20))
                     (and
                      (fqr-a22-memory-equal-p
                       t-5 nil t-4 nil)
                      (equal r-22 r-4)
                      (fqr-a22-memory-equal-p
                       t-5 m-10 t-9 nil)
                      (fqr-a22-le ctx zero r)
                      (fqr-a22-le ctx zero r-23)
                      (fqr-a22-is-finite32-p r)
                      (fqr-a22-is-finite32-p r-23))))))
             (and
              (fqr-a22-memory-equal-p
               t-4 nil t-2 nil)
              (if (fqr-a22-lt ctx r-16 r-17)
                  (and
                   (fqr-a22-memory-equal-p
                    t-6 nil t-4 nil)
                   (equal r-19 r-5)
                   (fqr-a22-memory-equal-p
                    t-6 m-7 t-9 nil)
                   (fqr-a22-le ctx zero r-1)
                   (fqr-a22-le ctx zero r-20)
                   (fqr-a22-is-finite32-p r-1)
                   (fqr-a22-is-finite32-p r-20))
                (and
                 (fqr-a22-memory-equal-p
                  t-5 nil t-4 nil)
                 (equal r-22 r-4)
                 (fqr-a22-memory-equal-p
                  t-5 m-10 t-9 nil)
                 (fqr-a22-le ctx zero r)
                 (fqr-a22-le ctx zero r-23)
                 (fqr-a22-is-finite32-p r)
                 (fqr-a22-is-finite32-p r-23))))))))
       (equal
        (fqr-a22-max2-transposed-memory-quaternion
         ctx one t-9 a)
        (fqr-a22-quaternion-of-memory
         t-9 nil a-1))))))

(value-triple :itpeval-statement-checked)
:q
