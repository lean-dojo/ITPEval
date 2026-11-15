;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/airborne/float_rmat_integrate_fi/float_rmat_integrate_fi_Why3_ide_VCfloat_rmat_integrate_fi_call_float_rmat_comp_pre_2_goal0:
;; writable nine-cell matrix storage, valid three-cell rate storage, and the
;; stated region, linkage, and float conditions imply read-valid finite
;; storage for the matrix. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars are represented by an arbitrary real closed ordered field.  The
;; verification condition only reads real-valued memory cells, but retaining
;; this structure preserves the source map addr -> real without restricting
;; its range to ACL2's rational numbers.

(defstub fri-fi-real-op (ctx x) t)
(defstub fri-fi-add-op (ctx x y) t)
(defstub fri-fi-mul-op (ctx x y) t)
(defstub fri-fi-neg-op (ctx x) t)
(defstub fri-fi-inv-op (ctx x) t)
(defstub fri-fi-lt-op (ctx x y) t)

(defun fri-fi-real-p (ctx x)
  (if (fri-fi-real-op ctx x) t nil))

(defun fri-fi-add (ctx x y)
  (fri-fi-add-op ctx x y))

(defun fri-fi-mul (ctx x y)
  (fri-fi-mul-op ctx x y))

(defun fri-fi-neg (ctx x)
  (fri-fi-neg-op ctx x))

(defun fri-fi-inv (ctx x)
  (fri-fi-inv-op ctx x))

(defun fri-fi-lt (ctx x y)
  (if (fri-fi-lt-op ctx x y) t nil))

(defun fri-fi-le (ctx x y)
  (not (fri-fi-lt ctx y x)))

(defun-sk fri-fi-field-laws-p (ctx zero one)
  (forall (x y z)
    (implies
     (and
      (fri-fi-real-p ctx x)
      (fri-fi-real-p ctx y)
      (fri-fi-real-p ctx z))
     (and
      (fri-fi-real-p ctx (fri-fi-add ctx x y))
      (fri-fi-real-p ctx (fri-fi-mul ctx x y))
      (fri-fi-real-p ctx (fri-fi-neg ctx x))
      (fri-fi-real-p ctx (fri-fi-inv ctx x))
      (equal
       (fri-fi-add ctx (fri-fi-add ctx x y) z)
       (fri-fi-add ctx x (fri-fi-add ctx y z)))
      (equal
       (fri-fi-add ctx x y)
       (fri-fi-add ctx y x))
      (equal (fri-fi-add ctx x zero) x)
      (equal
       (fri-fi-add ctx x (fri-fi-neg ctx x))
       zero)
      (equal
       (fri-fi-mul ctx (fri-fi-mul ctx x y) z)
       (fri-fi-mul ctx x (fri-fi-mul ctx y z)))
      (equal
       (fri-fi-mul ctx x y)
       (fri-fi-mul ctx y x))
      (equal (fri-fi-mul ctx x one) x)
      (equal (fri-fi-inv ctx zero) zero)
      (implies
       (not (equal x zero))
       (equal
        (fri-fi-mul ctx x (fri-fi-inv ctx x))
        one))
      (equal
       (fri-fi-mul ctx x (fri-fi-add ctx y z))
       (fri-fi-add
        ctx
        (fri-fi-mul ctx x y)
        (fri-fi-mul ctx x z)))))))

(defun-sk fri-fi-order-laws-p (ctx zero)
  (forall (x y z)
    (implies
     (and
      (fri-fi-real-p ctx x)
      (fri-fi-real-p ctx y)
      (fri-fi-real-p ctx z))
     (and
      (not (fri-fi-lt ctx x x))
      (or
       (equal x y)
       (fri-fi-lt ctx x y)
       (fri-fi-lt ctx y x))
      (implies
       (and
        (fri-fi-lt ctx x y)
        (fri-fi-lt ctx y z))
       (fri-fi-lt ctx x z))
      (implies
       (fri-fi-lt ctx x y)
       (fri-fi-lt
        ctx
        (fri-fi-add ctx x z)
        (fri-fi-add ctx y z)))
      (implies
       (and
        (fri-fi-lt ctx zero x)
        (fri-fi-lt ctx zero y))
       (fri-fi-lt
        ctx zero (fri-fi-mul ctx x y)))))))

(defun-sk fri-fi-positive-square-root-exists-p
    (ctx zero x)
  (exists (root)
    (and
     (fri-fi-real-p ctx root)
     (fri-fi-le ctx zero root)
     (equal (fri-fi-mul ctx root root) x))))

(defun-sk fri-fi-positive-square-root-laws-p (ctx zero)
  (forall (x)
    (implies
     (and
      (fri-fi-real-p ctx x)
      (fri-fi-lt ctx zero x))
     (fri-fi-positive-square-root-exists-p
      ctx zero x))))

(defun fri-fi-real-coefficient-list-p (ctx coefficients)
  (if (consp coefficients)
      (and
       (fri-fi-real-p ctx (car coefficients))
       (fri-fi-real-coefficient-list-p
        ctx (cdr coefficients)))
    (equal coefficients nil)))

(defun fri-fi-poly-eval (ctx zero coefficients x)
  (if (consp coefficients)
      (fri-fi-add
       ctx
       (car coefficients)
       (fri-fi-mul
        ctx
        x
        (fri-fi-poly-eval
         ctx zero (cdr coefficients) x)))
    zero))

(defun-sk fri-fi-odd-polynomial-root-exists-p
    (ctx zero coefficients)
  (exists (root)
    (and
     (fri-fi-real-p ctx root)
     (equal
      (fri-fi-poly-eval
       ctx zero coefficients root)
      zero))))

(defun-sk fri-fi-odd-root-laws-p (ctx zero)
  (forall (coefficients degree)
    (implies
     (and
      (natp degree)
      (not (equal degree 0))
      (oddp degree)
      (true-listp coefficients)
      (consp coefficients)
      (equal (len coefficients) (+ 1 degree))
      (fri-fi-real-coefficient-list-p
       ctx coefficients)
      (not
       (equal
        (car (last coefficients))
        zero)))
     (fri-fi-odd-polynomial-root-exists-p
      ctx zero coefficients))))

(defun fri-fi-real-context-p (ctx zero one)
  (and
   (fri-fi-real-p ctx zero)
   (fri-fi-real-p ctx one)
   (not (equal zero one))
   (fri-fi-lt ctx zero one)
   (fri-fi-field-laws-p ctx zero one)
   (fri-fi-order-laws-p ctx zero)
   (fri-fi-positive-square-root-laws-p ctx zero)
   (fri-fi-odd-root-laws-p ctx zero)))

;; Addresses are exactly pairs of mathematical integers, matching the source
;; record's integer base and offset fields.

(defun fri-fi-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun fri-fi-address-base (address)
  (car address))

(defun fri-fi-address-offset (address)
  (cdr address))

(defun fri-fi-shift (address amount)
  (cons
   (fri-fi-address-base address)
   (+ (fri-fi-address-offset address) amount)))

;; Tagged conservative interfaces retain the source's arbitrary functions:
;; t : integer -> integer, t_1 : address -> real, region : integer -> integer,
;; and linked : (integer -> integer) -> proposition.

(defstub fri-fi-memory-at (memory-tag address) t)
(defstub fri-fi-malloc-at (malloc-tag index) t)
(defstub fri-fi-region-op (base) t)
(defstub fri-fi-linked-op (malloc-tag) t)

(defun-sk fri-fi-memory-function-p (ctx memory-tag)
  (forall (address)
    (implies
     (fri-fi-address-p address)
     (fri-fi-real-p
      ctx
      (fri-fi-memory-at memory-tag address)))))

(defun-sk fri-fi-malloc-function-p (malloc-tag)
  (forall (index)
    (implies
     (integerp index)
     (integerp
      (fri-fi-malloc-at malloc-tag index)))))

(defun-sk fri-fi-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (fri-fi-region-op base)))))

(defun fri-fi-linked-p (malloc-tag)
  (if (fri-fi-linked-op malloc-tag) t nil))

(defun fri-fi-valid-rw-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (< 0 (fri-fi-address-base address))
    (<= 0 (fri-fi-address-offset address))
    (<=
     (+ (fri-fi-address-offset address) length)
     (fri-fi-malloc-at
      malloc-tag
      (fri-fi-address-base address))))))

(defun fri-fi-valid-rd-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (fri-fi-address-base address)))
    (<= 0 (fri-fi-address-offset address))
    (<=
     (+ (fri-fi-address-offset address) length)
     (fri-fi-malloc-at
      malloc-tag
      (fri-fi-address-base address))))))

;; In the shared source theory IS_FLOAT32 is definitionally true, and the
;; supplied classification axiom makes IS_FINITE32 true for every real.

(defun fri-fi-is-float32-p (value)
  (declare (ignore value))
  t)

(defun fri-fi-is-finite32-p (value)
  (declare (ignore value))
  t)

(defun fri-fi-finite-floatrates-p
    (memory-tag address)
  (and
   (fri-fi-is-finite32-p
    (fri-fi-memory-at
     memory-tag (fri-fi-shift address 0)))
   (fri-fi-is-finite32-p
    (fri-fi-memory-at
     memory-tag (fri-fi-shift address 1)))
   (fri-fi-is-finite32-p
    (fri-fi-memory-at
     memory-tag (fri-fi-shift address 2)))))

(defun fri-fi-rvalid-floatrates-p
    (malloc-tag memory-tag address)
  (and
   (fri-fi-finite-floatrates-p
    memory-tag address)
   (fri-fi-valid-rd-p
    malloc-tag address 3)))

(defun fri-fi-finite-floatrmat-p
    (memory-tag address)
  (let ((base (fri-fi-shift address 0)))
    (and
     (fri-fi-is-finite32-p
      (fri-fi-memory-at
       memory-tag (fri-fi-shift base 0)))
     (fri-fi-is-finite32-p
      (fri-fi-memory-at
       memory-tag (fri-fi-shift base 1)))
     (fri-fi-is-finite32-p
      (fri-fi-memory-at
       memory-tag (fri-fi-shift base 2)))
     (fri-fi-is-finite32-p
      (fri-fi-memory-at
       memory-tag (fri-fi-shift base 3)))
     (fri-fi-is-finite32-p
      (fri-fi-memory-at
       memory-tag (fri-fi-shift base 4)))
     (fri-fi-is-finite32-p
      (fri-fi-memory-at
       memory-tag (fri-fi-shift base 5)))
     (fri-fi-is-finite32-p
      (fri-fi-memory-at
       memory-tag (fri-fi-shift base 6)))
     (fri-fi-is-finite32-p
      (fri-fi-memory-at
       memory-tag (fri-fi-shift base 7)))
     (fri-fi-is-finite32-p
      (fri-fi-memory-at
       memory-tag (fri-fi-shift base 8))))))

(defun fri-fi-rvalid-floatrmat-p
    (malloc-tag memory-tag address)
  (and
   (fri-fi-finite-floatrmat-p
    memory-tag address)
   (fri-fi-valid-rd-p
    malloc-tag address 9)))

(defun-sk
    ntp4vc-float-rmat-integrate-fi-call-float-rmat-comp-pre-2-goal0-statement
    ()
  (forall (ctx zero one a a-1 malloc-tag memory-tag)
    (implies
     (and
      (fri-fi-real-context-p ctx zero one)
      (fri-fi-address-p a)
      (fri-fi-address-p a-1)
      (fri-fi-malloc-function-p malloc-tag)
      (fri-fi-memory-function-p ctx memory-tag)
      (fri-fi-region-function-p))
     (implies
      (and
       (<=
        (fri-fi-region-op
         (fri-fi-address-base a))
        0)
       (<=
        (fri-fi-region-op
         (fri-fi-address-base a-1))
        0)
       (fri-fi-linked-p malloc-tag)
       (fri-fi-valid-rw-p malloc-tag a 9)
       (fri-fi-rvalid-floatrates-p
        malloc-tag memory-tag a-1)
       (fri-fi-is-float32-p
        (fri-fi-memory-at
         memory-tag (fri-fi-shift a-1 0)))
       (fri-fi-is-float32-p
        (fri-fi-memory-at
         memory-tag (fri-fi-shift a-1 1)))
       (fri-fi-is-float32-p
        (fri-fi-memory-at
         memory-tag (fri-fi-shift a-1 2))))
      (fri-fi-rvalid-floatrmat-p
       malloc-tag memory-tag a)))))

(value-triple :itpeval-statement-checked)

:q
