;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/airborne/float_quat_of_rmat/float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_trace_pos_post_goal12:
;; the positive-trace branch of a rotation-matrix-to-quaternion conversion
;; returns the specified real quaternion under the generated memory, branch,
;; and floating-value conditions. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars are presented as an arbitrary real closed ordered field.  The
;; source verification condition is first-order in field operations, order,
;; square root, addresses, and arbitrary tagged functions.  Real closed
;; fields are elementarily equivalent, so this preserves the statement over
;; the mathematical reals without restricting values to ACL2 rationals.

(defstub fqr-trace-real-op (ctx x) t)
(defstub fqr-trace-add-op (ctx x y) t)
(defstub fqr-trace-mul-op (ctx x y) t)
(defstub fqr-trace-neg-op (ctx x) t)
(defstub fqr-trace-inv-op (ctx x) t)
(defstub fqr-trace-lt-op (ctx x y) t)
(defstub fqr-trace-sqrt-op (ctx x) t)

(defun fqr-trace-real-p (ctx x)
  (if (fqr-trace-real-op ctx x) t nil))

(defun fqr-trace-add (ctx x y)
  (fqr-trace-add-op ctx x y))

(defun fqr-trace-mul (ctx x y)
  (fqr-trace-mul-op ctx x y))

(defun fqr-trace-neg (ctx x)
  (fqr-trace-neg-op ctx x))

(defun fqr-trace-inv (ctx x)
  (fqr-trace-inv-op ctx x))

(defun fqr-trace-sub (ctx x y)
  (fqr-trace-add ctx x (fqr-trace-neg ctx y)))

(defun fqr-trace-div (ctx x y)
  (fqr-trace-mul ctx x (fqr-trace-inv ctx y)))

(defun fqr-trace-lt (ctx x y)
  (if (fqr-trace-lt-op ctx x y) t nil))

(defun fqr-trace-le (ctx x y)
  (not (fqr-trace-lt ctx y x)))

(defun fqr-trace-sqrt (ctx x)
  (fqr-trace-sqrt-op ctx x))

(defun fqr-trace-two (ctx one)
  (fqr-trace-add ctx one one))

(defun fqr-trace-half (ctx one)
  (fqr-trace-div ctx one (fqr-trace-two ctx one)))

(defun fqr-trace-pow (ctx one x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      one
    (fqr-trace-mul
     ctx x (fqr-trace-pow ctx one x (1- n)))))

(defun fqr-trace-real-list-p (ctx coefficients)
  (if (consp coefficients)
      (and
       (fqr-trace-real-p ctx (car coefficients))
       (fqr-trace-real-list-p ctx (cdr coefficients)))
    (equal coefficients nil)))

(defun fqr-trace-poly-eval
    (ctx one coefficients degree x)
  (declare (xargs :measure (nfix degree)))
  (if (zp degree)
      (nth 0 coefficients)
    (fqr-trace-add
     ctx
     (fqr-trace-poly-eval
      ctx one coefficients (1- degree) x)
     (fqr-trace-mul
      ctx
      (nth degree coefficients)
      (fqr-trace-pow ctx one x degree)))))

(defun-sk fqr-trace-field-laws-p (ctx zero one)
  (forall (x y z)
    (implies
     (and
      (fqr-trace-real-p ctx x)
      (fqr-trace-real-p ctx y)
      (fqr-trace-real-p ctx z))
     (and
      (fqr-trace-real-p ctx (fqr-trace-add ctx x y))
      (fqr-trace-real-p ctx (fqr-trace-mul ctx x y))
      (fqr-trace-real-p ctx (fqr-trace-neg ctx x))
      (fqr-trace-real-p ctx (fqr-trace-inv ctx x))
      (equal
       (fqr-trace-add ctx (fqr-trace-add ctx x y) z)
       (fqr-trace-add ctx x (fqr-trace-add ctx y z)))
      (equal
       (fqr-trace-add ctx x y)
       (fqr-trace-add ctx y x))
      (equal (fqr-trace-add ctx x zero) x)
      (equal
       (fqr-trace-add ctx x (fqr-trace-neg ctx x))
       zero)
      (equal
       (fqr-trace-mul ctx (fqr-trace-mul ctx x y) z)
       (fqr-trace-mul ctx x (fqr-trace-mul ctx y z)))
      (equal
       (fqr-trace-mul ctx x y)
       (fqr-trace-mul ctx y x))
      (equal (fqr-trace-mul ctx x one) x)
      (equal (fqr-trace-inv ctx zero) zero)
      (implies
       (not (equal x zero))
       (equal
        (fqr-trace-mul ctx x (fqr-trace-inv ctx x))
        one))
      (equal
       (fqr-trace-mul ctx x (fqr-trace-add ctx y z))
       (fqr-trace-add
        ctx
        (fqr-trace-mul ctx x y)
        (fqr-trace-mul ctx x z)))))))

(defun-sk fqr-trace-order-laws-p (ctx zero)
  (forall (x y z)
    (implies
     (and
      (fqr-trace-real-p ctx x)
      (fqr-trace-real-p ctx y)
      (fqr-trace-real-p ctx z))
     (and
      (not (fqr-trace-lt ctx x x))
      (or
       (equal x y)
       (fqr-trace-lt ctx x y)
       (fqr-trace-lt ctx y x))
      (implies
       (and
        (fqr-trace-lt ctx x y)
        (fqr-trace-lt ctx y z))
       (fqr-trace-lt ctx x z))
      (implies
       (fqr-trace-lt ctx x y)
       (fqr-trace-lt
        ctx
        (fqr-trace-add ctx x z)
        (fqr-trace-add ctx y z)))
      (implies
       (and
        (fqr-trace-lt ctx zero x)
        (fqr-trace-lt ctx zero y))
       (fqr-trace-lt
        ctx zero (fqr-trace-mul ctx x y)))))))

(defun-sk fqr-trace-sqrt-laws-p (ctx zero)
  (forall (x)
    (implies
     (fqr-trace-real-p ctx x)
     (and
      (fqr-trace-real-p ctx (fqr-trace-sqrt ctx x))
      (if (fqr-trace-lt ctx x zero)
          (equal (fqr-trace-sqrt ctx x) zero)
        (and
         (fqr-trace-le ctx zero (fqr-trace-sqrt ctx x))
         (equal
          (fqr-trace-mul
           ctx
           (fqr-trace-sqrt ctx x)
           (fqr-trace-sqrt ctx x))
          x)))))))

(defun fqr-trace-polynomial-coefficients-p
    (ctx coefficients degree)
  (and
   (natp degree)
   (equal (len coefficients) (+ 1 degree))
   (fqr-trace-real-list-p ctx coefficients)))

(defun-sk fqr-trace-odd-polynomial-root-exists-p
    (ctx zero one coefficients degree)
  (exists (root)
    (and
     (fqr-trace-real-p ctx root)
     (equal
      (fqr-trace-poly-eval
       ctx one coefficients degree root)
      zero))))

(defun-sk fqr-trace-odd-root-laws-p (ctx zero one)
  (forall (coefficients degree)
    (implies
     (and
      (not (equal degree 0))
      (oddp degree)
      (fqr-trace-polynomial-coefficients-p
       ctx coefficients degree)
      (not
       (equal (nth degree coefficients) zero)))
     (fqr-trace-odd-polynomial-root-exists-p
      ctx zero one coefficients degree))))

(defun fqr-trace-real-context-p (ctx zero one)
  (and
   (fqr-trace-real-p ctx zero)
   (fqr-trace-real-p ctx one)
   (not (equal zero one))
   (fqr-trace-lt ctx zero one)
   (fqr-trace-field-laws-p ctx zero one)
   (fqr-trace-order-laws-p ctx zero)
   (fqr-trace-sqrt-laws-p ctx zero)
   (fqr-trace-odd-root-laws-p ctx zero one)))

;; Addresses are the source record of an integer base and integer offset.

(defun fqr-trace-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun fqr-trace-address-base (address)
  (car address))

(defun fqr-trace-address-offset (address)
  (cdr address))

(defun fqr-trace-shift (address amount)
  (cons
   (fqr-trace-address-base address)
   (+ (fqr-trace-address-offset address) amount)))

;; Tagged conservative interfaces retain the source's arbitrary functions.

(defstub fqr-trace-memory-at (memory-tag address) t)
(defstub fqr-trace-malloc-at (malloc-tag index) t)
(defstub fqr-trace-region-op (base) t)
(defstub fqr-trace-linked-op (malloc-tag) t)

(defun-sk fqr-trace-memory-function-p (ctx memory-tag)
  (forall (address)
    (implies
     (fqr-trace-address-p address)
     (fqr-trace-real-p
      ctx
      (fqr-trace-memory-at memory-tag address)))))

(defun-sk fqr-trace-malloc-function-p (malloc-tag)
  (forall (index)
    (implies
     (integerp index)
     (integerp
      (fqr-trace-malloc-at malloc-tag index)))))

(defun-sk fqr-trace-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (fqr-trace-region-op base)))))

(defun fqr-trace-linked-p (malloc-tag)
  (if (fqr-trace-linked-op malloc-tag) t nil))

(defun fqr-trace-memory-read (memory-tag updates address)
  (let ((entry (assoc-equal address updates)))
    (if entry
        (cdr entry)
      (fqr-trace-memory-at memory-tag address))))

(defun fqr-trace-memory-write (updates address value)
  (cons (cons address value) updates))

(defun-sk fqr-trace-memory-equal-p
    (left-tag left-updates right-tag right-updates)
  (forall (address)
    (implies
     (fqr-trace-address-p address)
     (equal
      (fqr-trace-memory-read
       left-tag left-updates address)
      (fqr-trace-memory-read
       right-tag right-updates address)))))

(defun fqr-trace-valid-rw-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (< 0 (fqr-trace-address-base address))
    (<= 0 (fqr-trace-address-offset address))
    (<=
     (+ (fqr-trace-address-offset address) length)
     (fqr-trace-malloc-at
      malloc-tag
      (fqr-trace-address-base address))))))

(defun fqr-trace-valid-rd-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (fqr-trace-address-base address)))
    (<= 0 (fqr-trace-address-offset address))
    (<=
     (+ (fqr-trace-address-offset address) length)
     (fqr-trace-malloc-at
      malloc-tag
      (fqr-trace-address-base address))))))

(defun fqr-trace-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (fqr-trace-address-base left)
     (fqr-trace-address-base right)))
   (<=
    (+ (fqr-trace-address-offset right) right-length)
    (fqr-trace-address-offset left))
   (<=
    (+ (fqr-trace-address-offset left) left-length)
    (fqr-trace-address-offset right))))

;; In the shared source theory IS_FLOAT32 is definitionally true, while the
;; supplied classification axiom makes IS_FINITE32 true for every real.

(defun fqr-trace-is-float32-p (value)
  (declare (ignore value))
  t)

(defun fqr-trace-is-finite32-p (value)
  (declare (ignore value))
  t)

(defun fqr-trace-finite-floatrmat-p
    (memory-tag updates address)
  (and
   (fqr-trace-is-finite32-p
    (fqr-trace-memory-read
     memory-tag updates (fqr-trace-shift address 0)))
   (fqr-trace-is-finite32-p
    (fqr-trace-memory-read
     memory-tag updates (fqr-trace-shift address 1)))
   (fqr-trace-is-finite32-p
    (fqr-trace-memory-read
     memory-tag updates (fqr-trace-shift address 2)))
   (fqr-trace-is-finite32-p
    (fqr-trace-memory-read
     memory-tag updates (fqr-trace-shift address 3)))
   (fqr-trace-is-finite32-p
    (fqr-trace-memory-read
     memory-tag updates (fqr-trace-shift address 4)))
   (fqr-trace-is-finite32-p
    (fqr-trace-memory-read
     memory-tag updates (fqr-trace-shift address 5)))
   (fqr-trace-is-finite32-p
    (fqr-trace-memory-read
     memory-tag updates (fqr-trace-shift address 6)))
   (fqr-trace-is-finite32-p
    (fqr-trace-memory-read
     memory-tag updates (fqr-trace-shift address 7)))
   (fqr-trace-is-finite32-p
    (fqr-trace-memory-read
     memory-tag updates (fqr-trace-shift address 8)))))

(defun fqr-trace-rvalid-floatrmat-p
    (malloc-tag memory-tag updates address)
  (and
   (fqr-trace-finite-floatrmat-p
    memory-tag updates address)
   (fqr-trace-valid-rd-p malloc-tag address 9)))

;; Matrices use row-major nine-tuples and quaternions use scalar/x/y/z
;; four-tuples, exactly matching the source records.

(defun fqr-trace-matrix
    (a00 a01 a02 a10 a11 a12 a20 a21 a22)
  (list a00 a01 a02 a10 a11 a12 a20 a21 a22))

(defun fqr-trace-matrix-entry (matrix row column)
  (nth (+ (* 3 row) column) matrix))

(defun fqr-trace-matrix-of-memory
    (memory-tag updates address)
  (fqr-trace-matrix
   (fqr-trace-memory-read
    memory-tag updates (fqr-trace-shift address 0))
   (fqr-trace-memory-read
    memory-tag updates (fqr-trace-shift address 1))
   (fqr-trace-memory-read
    memory-tag updates (fqr-trace-shift address 2))
   (fqr-trace-memory-read
    memory-tag updates (fqr-trace-shift address 3))
   (fqr-trace-memory-read
    memory-tag updates (fqr-trace-shift address 4))
   (fqr-trace-memory-read
    memory-tag updates (fqr-trace-shift address 5))
   (fqr-trace-memory-read
    memory-tag updates (fqr-trace-shift address 6))
   (fqr-trace-memory-read
    memory-tag updates (fqr-trace-shift address 7))
   (fqr-trace-memory-read
    memory-tag updates (fqr-trace-shift address 8))))

(defun fqr-trace-matrix-transpose (matrix)
  (fqr-trace-matrix
   (fqr-trace-matrix-entry matrix 0 0)
   (fqr-trace-matrix-entry matrix 1 0)
   (fqr-trace-matrix-entry matrix 2 0)
   (fqr-trace-matrix-entry matrix 0 1)
   (fqr-trace-matrix-entry matrix 1 1)
   (fqr-trace-matrix-entry matrix 2 1)
   (fqr-trace-matrix-entry matrix 0 2)
   (fqr-trace-matrix-entry matrix 1 2)
   (fqr-trace-matrix-entry matrix 2 2)))

(defun fqr-trace-dot3 (ctx a b c x y z)
  (fqr-trace-add
   ctx
   (fqr-trace-add
    ctx
    (fqr-trace-mul ctx a x)
    (fqr-trace-mul ctx b y))
   (fqr-trace-mul ctx c z)))

(defun fqr-trace-matrix-mul (ctx left right)
  (fqr-trace-matrix
   (fqr-trace-dot3
    ctx
    (fqr-trace-matrix-entry left 0 0)
    (fqr-trace-matrix-entry left 0 1)
    (fqr-trace-matrix-entry left 0 2)
    (fqr-trace-matrix-entry right 0 0)
    (fqr-trace-matrix-entry right 1 0)
    (fqr-trace-matrix-entry right 2 0))
   (fqr-trace-dot3
    ctx
    (fqr-trace-matrix-entry left 0 0)
    (fqr-trace-matrix-entry left 0 1)
    (fqr-trace-matrix-entry left 0 2)
    (fqr-trace-matrix-entry right 0 1)
    (fqr-trace-matrix-entry right 1 1)
    (fqr-trace-matrix-entry right 2 1))
   (fqr-trace-dot3
    ctx
    (fqr-trace-matrix-entry left 0 0)
    (fqr-trace-matrix-entry left 0 1)
    (fqr-trace-matrix-entry left 0 2)
    (fqr-trace-matrix-entry right 0 2)
    (fqr-trace-matrix-entry right 1 2)
    (fqr-trace-matrix-entry right 2 2))
   (fqr-trace-dot3
    ctx
    (fqr-trace-matrix-entry left 1 0)
    (fqr-trace-matrix-entry left 1 1)
    (fqr-trace-matrix-entry left 1 2)
    (fqr-trace-matrix-entry right 0 0)
    (fqr-trace-matrix-entry right 1 0)
    (fqr-trace-matrix-entry right 2 0))
   (fqr-trace-dot3
    ctx
    (fqr-trace-matrix-entry left 1 0)
    (fqr-trace-matrix-entry left 1 1)
    (fqr-trace-matrix-entry left 1 2)
    (fqr-trace-matrix-entry right 0 1)
    (fqr-trace-matrix-entry right 1 1)
    (fqr-trace-matrix-entry right 2 1))
   (fqr-trace-dot3
    ctx
    (fqr-trace-matrix-entry left 1 0)
    (fqr-trace-matrix-entry left 1 1)
    (fqr-trace-matrix-entry left 1 2)
    (fqr-trace-matrix-entry right 0 2)
    (fqr-trace-matrix-entry right 1 2)
    (fqr-trace-matrix-entry right 2 2))
   (fqr-trace-dot3
    ctx
    (fqr-trace-matrix-entry left 2 0)
    (fqr-trace-matrix-entry left 2 1)
    (fqr-trace-matrix-entry left 2 2)
    (fqr-trace-matrix-entry right 0 0)
    (fqr-trace-matrix-entry right 1 0)
    (fqr-trace-matrix-entry right 2 0))
   (fqr-trace-dot3
    ctx
    (fqr-trace-matrix-entry left 2 0)
    (fqr-trace-matrix-entry left 2 1)
    (fqr-trace-matrix-entry left 2 2)
    (fqr-trace-matrix-entry right 0 1)
    (fqr-trace-matrix-entry right 1 1)
    (fqr-trace-matrix-entry right 2 1))
   (fqr-trace-dot3
    ctx
    (fqr-trace-matrix-entry left 2 0)
    (fqr-trace-matrix-entry left 2 1)
    (fqr-trace-matrix-entry left 2 2)
    (fqr-trace-matrix-entry right 0 2)
    (fqr-trace-matrix-entry right 1 2)
    (fqr-trace-matrix-entry right 2 2))))

(defun fqr-trace-identity-matrix (zero one)
  (fqr-trace-matrix
   one zero zero
   zero one zero
   zero zero one))

(defun fqr-trace-rotation-matrix-p (ctx zero one matrix)
  (equal
   (fqr-trace-matrix-mul
    ctx matrix (fqr-trace-matrix-transpose matrix))
   (fqr-trace-identity-matrix zero one)))

(defun fqr-trace-determinant (ctx matrix)
  (let*
      ((a00 (fqr-trace-matrix-entry matrix 0 0))
       (a01 (fqr-trace-matrix-entry matrix 0 1))
       (a02 (fqr-trace-matrix-entry matrix 0 2))
       (a10 (fqr-trace-matrix-entry matrix 1 0))
       (a11 (fqr-trace-matrix-entry matrix 1 1))
       (a12 (fqr-trace-matrix-entry matrix 1 2))
       (a20 (fqr-trace-matrix-entry matrix 2 0))
       (a21 (fqr-trace-matrix-entry matrix 2 1))
       (a22 (fqr-trace-matrix-entry matrix 2 2)))
    (fqr-trace-sub
     ctx
     (fqr-trace-sub
      ctx
      (fqr-trace-sub
       ctx
       (fqr-trace-add
        ctx
        (fqr-trace-add
         ctx
         (fqr-trace-mul
          ctx (fqr-trace-mul ctx a00 a11) a22)
         (fqr-trace-mul
          ctx (fqr-trace-mul ctx a01 a12) a20))
        (fqr-trace-mul
         ctx (fqr-trace-mul ctx a02 a10) a21))
       (fqr-trace-mul
        ctx (fqr-trace-mul ctx a00 a12) a21))
      (fqr-trace-mul
       ctx (fqr-trace-mul ctx a01 a10) a22))
     (fqr-trace-mul
      ctx (fqr-trace-mul ctx a02 a11) a20))))

(defun fqr-trace-special-orthogonal-p (ctx one matrix)
  (equal (fqr-trace-determinant ctx matrix) one))

(defun fqr-trace-trace (ctx matrix)
  (fqr-trace-add
   ctx
   (fqr-trace-add
    ctx
    (fqr-trace-matrix-entry matrix 0 0)
    (fqr-trace-matrix-entry matrix 1 1))
   (fqr-trace-matrix-entry matrix 2 2)))

(defun fqr-trace-quaternion (qi qx qy qz)
  (list qi qx qy qz))

(defun fqr-trace-quaternion-of-memory
    (memory-tag updates address)
  (fqr-trace-quaternion
   (fqr-trace-memory-read
    memory-tag updates (fqr-trace-shift address 0))
   (fqr-trace-memory-read
    memory-tag updates (fqr-trace-shift address 1))
   (fqr-trace-memory-read
    memory-tag updates (fqr-trace-shift address 2))
   (fqr-trace-memory-read
    memory-tag updates (fqr-trace-shift address 3))))

(defun fqr-trace-positive-quaternion (ctx one matrix)
  (let*
      ((a00 (fqr-trace-matrix-entry matrix 0 0))
       (a01 (fqr-trace-matrix-entry matrix 0 1))
       (a02 (fqr-trace-matrix-entry matrix 0 2))
       (a10 (fqr-trace-matrix-entry matrix 1 0))
       (a11 (fqr-trace-matrix-entry matrix 1 1))
       (a12 (fqr-trace-matrix-entry matrix 1 2))
       (a20 (fqr-trace-matrix-entry matrix 2 0))
       (a21 (fqr-trace-matrix-entry matrix 2 1))
       (a22 (fqr-trace-matrix-entry matrix 2 2))
       (scale
        (fqr-trace-div
         ctx
         (fqr-trace-half ctx one)
         (fqr-trace-sqrt
          ctx
          (fqr-trace-add
           ctx
           one
           (fqr-trace-add
            ctx
            (fqr-trace-add ctx a00 a11)
            a22)))))
       (four
        (fqr-trace-mul
         ctx
         (fqr-trace-two ctx one)
         (fqr-trace-two ctx one))))
    (fqr-trace-quaternion
     (fqr-trace-div
      ctx (fqr-trace-div ctx one four) scale)
     (fqr-trace-mul
      ctx (fqr-trace-sub ctx a21 a12) scale)
     (fqr-trace-mul
      ctx (fqr-trace-sub ctx a02 a20) scale)
     (fqr-trace-mul
      ctx (fqr-trace-sub ctx a10 a01) scale))))

(defun fqr-trace-positive-transposed-memory-quaternion
    (ctx one memory-tag address)
  (fqr-trace-positive-quaternion
   ctx
   one
   (fqr-trace-matrix-transpose
    (fqr-trace-matrix-of-memory
     memory-tag nil address))))

(defun
    ntp4vc-float-quat-of-rmat-trace-pos-post-goal12-statement
    (ctx zero one
         a t-1 a-1 t-8 r-3 r-7 t-7 r-6 r-2 t-4 r-1
         t-6 r-5 r t-5 r-4 malloc-tag t-9 t-2 t-3)
   (implies
    (and
     (fqr-trace-real-context-p ctx zero one)
     (fqr-trace-address-p a)
     (fqr-trace-address-p a-1)
     (fqr-trace-memory-function-p ctx t-1)
     (fqr-trace-memory-function-p ctx t-8)
     (fqr-trace-memory-function-p ctx t-7)
     (fqr-trace-memory-function-p ctx t-4)
     (fqr-trace-memory-function-p ctx t-6)
     (fqr-trace-memory-function-p ctx t-5)
     (fqr-trace-memory-function-p ctx t-9)
     (fqr-trace-memory-function-p ctx t-2)
     (fqr-trace-memory-function-p ctx t-3)
     (fqr-trace-malloc-function-p malloc-tag)
     (fqr-trace-region-function-p)
     (fqr-trace-real-p ctx r-3)
     (fqr-trace-real-p ctx r-7)
     (fqr-trace-real-p ctx r-6)
     (fqr-trace-real-p ctx r-2)
     (fqr-trace-real-p ctx r-1)
     (fqr-trace-real-p ctx r-5)
     (fqr-trace-real-p ctx r)
     (fqr-trace-real-p ctx r-4))
    (let*
        ((a-2 (fqr-trace-shift a 0))
         (a-3 (fqr-trace-shift a-2 0))
         (r-8 (fqr-trace-memory-read t-1 nil a-3))
         (a-4 (fqr-trace-shift a-2 8))
         (r-10 (fqr-trace-memory-read t-1 nil a-4))
         (a-5 (fqr-trace-shift a-2 4))
         (r-9 (fqr-trace-memory-read t-1 nil a-5))
         (matrix-6
          (fqr-trace-matrix-of-memory t-1 nil a))
         (r-11
          (fqr-trace-add
           ctx
           (fqr-trace-add ctx r-8 r-9)
           r-10))
         (a-7 (fqr-trace-shift a-1 0))
         (m
          (fqr-trace-memory-write
           nil
           a-7
           (fqr-trace-mul
            ctx (fqr-trace-half ctx one) r-3)))
         (a-8 (fqr-trace-shift a-1 1))
         (a-9 (fqr-trace-shift a-2 5))
         (a-10 (fqr-trace-shift a-2 7))
         (m-1
          (fqr-trace-memory-write
           m
           a-8
           (fqr-trace-div
            ctx
            (fqr-trace-sub
             ctx
             (fqr-trace-memory-read t-8 m a-9)
             (fqr-trace-memory-read t-8 m a-10))
            r-7)))
         (a-11 (fqr-trace-shift a-1 2))
         (a-12 (fqr-trace-shift a-2 6))
         (a-13 (fqr-trace-shift a-2 2))
         (m-2
          (fqr-trace-memory-write
           m-1
           a-11
           (fqr-trace-div
            ctx
            (fqr-trace-sub
             ctx
             (fqr-trace-memory-read t-8 m-1 a-12)
             (fqr-trace-memory-read t-8 m-1 a-13))
            r-7)))
         (a-14 (fqr-trace-shift a-1 3))
         (a-15 (fqr-trace-shift a-2 1))
         (a-16 (fqr-trace-shift a-2 3))
         (r-13
          (fqr-trace-add
           ctx
           one
           (fqr-trace-add
            ctx
            (fqr-trace-add
             ctx
             (fqr-trace-memory-read t-8 nil a-3)
             (fqr-trace-memory-read t-8 nil a-5))
            (fqr-trace-memory-read t-8 nil a-4))))
         (m-3a
          (fqr-trace-memory-write
           nil
           a-7
           (fqr-trace-div
            ctx
            (fqr-trace-sub
             ctx
             (fqr-trace-memory-read t-7 nil a-9)
             (fqr-trace-memory-read t-7 nil a-10))
            r-6)))
         (m-3
          (fqr-trace-memory-write
           m-3a
           a-8
           (fqr-trace-mul
            ctx (fqr-trace-half ctx one) r-2)))
         (m-4
          (fqr-trace-memory-write
           m-3
           a-11
           (fqr-trace-div
            ctx
            (fqr-trace-add
             ctx
             (fqr-trace-memory-read t-7 m-3 a-15)
             (fqr-trace-memory-read t-7 m-3 a-16))
            r-6)))
         (r-15
          (fqr-trace-add
           ctx
           (fqr-trace-sub
            ctx
            (fqr-trace-sub
             ctx
             (fqr-trace-memory-read t-7 nil a-3)
             (fqr-trace-memory-read t-7 nil a-5))
            (fqr-trace-memory-read t-7 nil a-4))
           one))
         (r-16 (fqr-trace-memory-read t-4 nil a-4))
         (r-17 (fqr-trace-memory-read t-4 nil a-5))
         (r-19
          (fqr-trace-mul ctx (fqr-trace-two ctx one) r-1))
         (m-5
          (fqr-trace-memory-write
           nil
           a-7
           (fqr-trace-div
            ctx
            (fqr-trace-sub
             ctx
             (fqr-trace-memory-read t-6 nil a-12)
             (fqr-trace-memory-read t-6 nil a-13))
            r-5)))
         (m-6a
          (fqr-trace-memory-write
           m-5
           a-8
           (fqr-trace-div
            ctx
            (fqr-trace-add
             ctx
             (fqr-trace-memory-read t-6 m-5 a-15)
             (fqr-trace-memory-read t-6 m-5 a-16))
            r-5)))
         (m-6
          (fqr-trace-memory-write
           m-6a
           a-11
           (fqr-trace-mul
            ctx (fqr-trace-half ctx one) r-1)))
         (m-7
          (fqr-trace-memory-write
           m-6
           a-14
           (fqr-trace-div
            ctx
            (fqr-trace-add
             ctx
             (fqr-trace-memory-read t-6 m-6 a-9)
             (fqr-trace-memory-read t-6 m-6 a-10))
            r-5)))
         (r-20
          (fqr-trace-add
           ctx
           (fqr-trace-sub
            ctx
            (fqr-trace-sub
             ctx
             (fqr-trace-memory-read t-6 nil a-5)
             (fqr-trace-memory-read t-6 nil a-3))
            (fqr-trace-memory-read t-6 nil a-4))
           one))
         (r-22
          (fqr-trace-mul ctx (fqr-trace-two ctx one) r))
         (m-8
          (fqr-trace-memory-write
           nil
           a-7
           (fqr-trace-div
            ctx
            (fqr-trace-sub
             ctx
             (fqr-trace-memory-read t-5 nil a-15)
             (fqr-trace-memory-read t-5 nil a-16))
            r-4)))
         (m-9
          (fqr-trace-memory-write
           m-8
           a-8
           (fqr-trace-div
            ctx
            (fqr-trace-add
             ctx
             (fqr-trace-memory-read t-5 m-8 a-12)
             (fqr-trace-memory-read t-5 m-8 a-13))
            r-4)))
         (m-10a
          (fqr-trace-memory-write
           m-9
           a-11
           (fqr-trace-div
            ctx
            (fqr-trace-add
             ctx
             (fqr-trace-memory-read t-5 m-9 a-9)
             (fqr-trace-memory-read t-5 m-9 a-10))
            r-4)))
         (m-10
          (fqr-trace-memory-write
           m-10a
           a-14
           (fqr-trace-mul
            ctx (fqr-trace-half ctx one) r)))
         (r-23
          (fqr-trace-add
           ctx
           (fqr-trace-sub
            ctx
            (fqr-trace-sub
             ctx
             (fqr-trace-memory-read t-5 nil a-4)
             (fqr-trace-memory-read t-5 nil a-3))
            (fqr-trace-memory-read t-5 nil a-5))
           one))
         (m-2-final
          (fqr-trace-memory-write
           m-2
           a-14
           (fqr-trace-div
            ctx
            (fqr-trace-sub
             ctx
             (fqr-trace-memory-read t-8 m-2 a-15)
             (fqr-trace-memory-read t-8 m-2 a-16))
            r-7)))
         (m-4-final
          (fqr-trace-memory-write
           m-4
           a-14
           (fqr-trace-div
            ctx
            (fqr-trace-add
             ctx
             (fqr-trace-memory-read t-7 m-4 a-12)
             (fqr-trace-memory-read t-7 m-4 a-13))
            r-6))))
      (implies
       (and
        (fqr-trace-lt
         ctx zero (fqr-trace-trace ctx matrix-6))
        (<= (fqr-trace-region-op
             (fqr-trace-address-base a))
            0)
        (<= (fqr-trace-region-op
             (fqr-trace-address-base a-1))
            0)
        (fqr-trace-linked-p malloc-tag)
        (fqr-trace-is-float32-p r)
        (fqr-trace-is-float32-p r-1)
        (fqr-trace-is-float32-p r-2)
        (fqr-trace-is-float32-p r-3)
        (fqr-trace-is-float32-p r-4)
        (fqr-trace-is-float32-p r-5)
        (fqr-trace-is-float32-p r-6)
        (fqr-trace-is-float32-p r-7)
        (fqr-trace-valid-rw-p malloc-tag a-1 4)
        (fqr-trace-rvalid-floatrmat-p
         malloc-tag t-1 nil a)
        (fqr-trace-separated-p a 9 a-1 4)
        (fqr-trace-rotation-matrix-p
         ctx zero one matrix-6)
        (fqr-trace-special-orthogonal-p
         ctx one matrix-6)
        (fqr-trace-is-float32-p r-8)
        (fqr-trace-is-float32-p r-10)
        (fqr-trace-is-float32-p r-9)
        (fqr-trace-is-float32-p r-11)
        (if (fqr-trace-lt ctx zero r-11)
            (and
             (fqr-trace-memory-equal-p
              t-8 nil t-1 nil)
             (equal
              (fqr-trace-mul
               ctx (fqr-trace-two ctx one) r-3)
              r-7)
             (fqr-trace-memory-equal-p
              t-8 m-2-final t-9 nil)
             (fqr-trace-le ctx zero r-3)
             (fqr-trace-le ctx zero r-13)
             (fqr-trace-is-finite32-p r-3)
             (fqr-trace-is-finite32-p r-13))
          (and
           (fqr-trace-memory-equal-p
            t-2 nil t-1 nil)
           (if
               (fqr-trace-lt
                ctx
                (fqr-trace-memory-read t-2 nil a-5)
                (fqr-trace-memory-read t-2 nil a-3))
               (and
                (fqr-trace-memory-equal-p
                 t-3 nil t-2 nil)
                (if
                    (fqr-trace-lt
                     ctx
                     (fqr-trace-memory-read t-3 nil a-4)
                     (fqr-trace-memory-read t-3 nil a-3))
                    (and
                     (fqr-trace-memory-equal-p
                      t-7 nil t-3 nil)
                     (equal
                      (fqr-trace-mul
                       ctx
                       (fqr-trace-two ctx one)
                       r-2)
                      r-6)
                     (fqr-trace-memory-equal-p
                      t-7 m-4-final t-9 nil)
                     (fqr-trace-le ctx zero r-2)
                     (fqr-trace-le ctx zero r-15)
                     (fqr-trace-is-finite32-p r-2)
                     (fqr-trace-is-finite32-p r-15))
                  (and
                   (fqr-trace-memory-equal-p
                    t-4 nil t-3 nil)
                   (if (fqr-trace-lt ctx r-16 r-17)
                       (and
                        (fqr-trace-memory-equal-p
                         t-6 nil t-4 nil)
                        (equal r-19 r-5)
                        (fqr-trace-memory-equal-p
                         t-6 m-7 t-9 nil)
                        (fqr-trace-le ctx zero r-1)
                        (fqr-trace-le ctx zero r-20)
                        (fqr-trace-is-finite32-p r-1)
                        (fqr-trace-is-finite32-p r-20))
                     (and
                      (fqr-trace-memory-equal-p
                       t-5 nil t-4 nil)
                      (equal r-22 r-4)
                      (fqr-trace-memory-equal-p
                       t-5 m-10 t-9 nil)
                      (fqr-trace-le ctx zero r)
                      (fqr-trace-le ctx zero r-23)
                      (fqr-trace-is-finite32-p r)
                      (fqr-trace-is-finite32-p r-23))))))
             (and
              (fqr-trace-memory-equal-p
               t-4 nil t-2 nil)
              (if (fqr-trace-lt ctx r-16 r-17)
                  (and
                   (fqr-trace-memory-equal-p
                    t-6 nil t-4 nil)
                   (equal r-19 r-5)
                   (fqr-trace-memory-equal-p
                    t-6 m-7 t-9 nil)
                   (fqr-trace-le ctx zero r-1)
                   (fqr-trace-le ctx zero r-20)
                   (fqr-trace-is-finite32-p r-1)
                   (fqr-trace-is-finite32-p r-20))
                (and
                 (fqr-trace-memory-equal-p
                  t-5 nil t-4 nil)
                 (equal r-22 r-4)
                 (fqr-trace-memory-equal-p
                  t-5 m-10 t-9 nil)
                 (fqr-trace-le ctx zero r)
                 (fqr-trace-le ctx zero r-23)
                 (fqr-trace-is-finite32-p r)
                 (fqr-trace-is-finite32-p r-23)))))))
        (equal r-3 (fqr-trace-sqrt ctx r-13)))
       (equal
        (fqr-trace-positive-transposed-memory-quaternion
         ctx one t-9 a)
        (fqr-trace-quaternion-of-memory
         t-9 nil a-1))))))

(value-triple :itpeval-statement-checked)
:q
