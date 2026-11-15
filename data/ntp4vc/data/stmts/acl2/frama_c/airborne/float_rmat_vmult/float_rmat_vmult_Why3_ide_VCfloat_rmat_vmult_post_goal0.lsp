;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/airborne/float_rmat_vmult/float_rmat_vmult_Why3_ide_VCfloat_rmat_vmult_post_goal0:
;; three sequential real dot-product writes compute multiplication of a
;; 3-by-3 matrix by a three-vector under the stated memory validity,
;; separation, and float-model conditions. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A polynomial is a canonical sorted list of
;; (sorted-monomial . integer-coefficient) pairs. Its indeterminates name
;; arbitrary initial memory cells. Equality of these polynomials is equivalent
;; to equality under every assignment of real values to the cells, so the
;; source's arbitrary function address -> real is preserved without narrowing
;; real values to ACL2 rationals.

(defun frtv-monomial-multiply (left right)
  (declare
   (xargs
    :measure (+ (acl2-count left) (acl2-count right))))
  (cond
   ((endp left) right)
   ((endp right) left)
   ((lexorder (car left) (car right))
    (cons
     (car left)
     (frtv-monomial-multiply (cdr left) right)))
   (t
    (cons
     (car right)
     (frtv-monomial-multiply left (cdr right))))))

(defun frtv-polynomial-insert
    (monomial coefficient polynomial)
  (cond
   ((equal coefficient 0) polynomial)
   ((endp polynomial)
    (list (cons monomial coefficient)))
   ((equal monomial (caar polynomial))
    (let ((sum (+ coefficient (cdar polynomial))))
      (if (equal sum 0)
          (cdr polynomial)
        (cons (cons monomial sum) (cdr polynomial)))))
   ((lexorder monomial (caar polynomial))
    (cons (cons monomial coefficient) polynomial))
   (t
    (cons
     (car polynomial)
     (frtv-polynomial-insert
      monomial coefficient (cdr polynomial))))))

(defun frtv-polynomial-add (left right)
  (if (endp left)
      right
    (frtv-polynomial-add
     (cdr left)
     (frtv-polynomial-insert
      (caar left) (cdar left) right))))

(defun frtv-polynomial-multiply-term
    (monomial coefficient polynomial)
  (if (endp polynomial)
      nil
    (frtv-polynomial-insert
     (frtv-monomial-multiply monomial (caar polynomial))
     (* coefficient (cdar polynomial))
     (frtv-polynomial-multiply-term
      monomial coefficient (cdr polynomial)))))

(defun frtv-polynomial-multiply (left right)
  (if (endp left)
      nil
    (frtv-polynomial-add
     (frtv-polynomial-multiply-term
      (caar left) (cdar left) right)
     (frtv-polynomial-multiply (cdr left) right))))

(defun frtv-polynomial-variable (name)
  (list (cons (list name) 1)))

(defun frtv-r-add (left right)
  (frtv-polynomial-add left right))

(defun frtv-r-multiply (left right)
  (frtv-polynomial-multiply left right))

(defun frtv-dot3 (a b c d e f)
  (frtv-r-add
   (frtv-r-add
    (frtv-r-multiply a b)
    (frtv-r-multiply c d))
   (frtv-r-multiply e f)))

;; Addresses are exactly pairs of mathematical integers, matching the source
;; address record with integer base and offset fields.

(defun frtv-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun frtv-address-base (address)
  (car address))

(defun frtv-address-offset (address)
  (cdr address))

(defun frtv-shift (address amount)
  (cons
   (frtv-address-base address)
   (+ (frtv-address-offset address) amount)))

;; These conservative interfaces preserve the arbitrary source allocation
;; function, the fixed arbitrary region function, and the linked predicate.

(defstub frtv-malloc-at (malloc-tag index) t)
(defstub frtv-region-op (base) t)
(defstub frtv-linked-op (malloc-tag) t)

(defun-sk frtv-malloc-function-p (malloc-tag)
  (forall (index)
    (implies
     (integerp index)
     (integerp (frtv-malloc-at malloc-tag index)))))

(defun-sk frtv-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (frtv-region-op base)))))

(defun frtv-linked-p (malloc-tag)
  (if (frtv-linked-op malloc-tag) t nil))

(defun frtv-valid-rw-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (< 0 (frtv-address-base address))
    (<= 0 (frtv-address-offset address))
    (<=
     (+ (frtv-address-offset address) length)
     (frtv-malloc-at malloc-tag (frtv-address-base address))))))

(defun frtv-valid-rd-p (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (frtv-address-base address)))
    (<= 0 (frtv-address-offset address))
    (<=
     (+ (frtv-address-offset address) length)
     (frtv-malloc-at malloc-tag (frtv-address-base address))))))

(defun frtv-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (frtv-address-base left)
     (frtv-address-base right)))
   (<=
    (+ (frtv-address-offset right) right-length)
    (frtv-address-offset left))
   (<=
    (+ (frtv-address-offset left) left-length)
    (frtv-address-offset right))))

;; An update list is newest first. Assoc-equal therefore implements the exact
;; successive function-update semantics, including every possible alias.

(defun frtv-memory-read (memory-tag updates address)
  (let ((entry (assoc-equal address updates)))
    (if entry
        (cdr entry)
      (frtv-polynomial-variable (list memory-tag address)))))

(defun frtv-memory-write (updates address value)
  (cons (cons address value) updates))

;; In the common source theory is_float32 is definitionally true, and the
;; supplied classification axiom makes is_finite32 true for every real.

(defun frtv-is-float32-p (value)
  (declare (ignore value))
  t)

(defun frtv-is-finite32-p (value)
  (declare (ignore value))
  t)

(defun frtv-finite-floatvect3-p
    (memory-tag updates address)
  (and
   (frtv-is-finite32-p
    (frtv-memory-read memory-tag updates (frtv-shift address 0)))
   (frtv-is-finite32-p
    (frtv-memory-read memory-tag updates (frtv-shift address 1)))
   (frtv-is-finite32-p
    (frtv-memory-read memory-tag updates (frtv-shift address 2)))))

(defun frtv-rvalid-floatvect3-p
    (malloc-tag memory-tag updates address)
  (and
   (frtv-finite-floatvect3-p memory-tag updates address)
   (frtv-valid-rd-p malloc-tag address 3)))

(defun frtv-finite-floatrmat-p
    (memory-tag updates address)
  (let ((base (frtv-shift address 0)))
    (and
     (frtv-is-finite32-p
      (frtv-memory-read memory-tag updates (frtv-shift base 0)))
     (frtv-is-finite32-p
      (frtv-memory-read memory-tag updates (frtv-shift base 1)))
     (frtv-is-finite32-p
      (frtv-memory-read memory-tag updates (frtv-shift base 2)))
     (frtv-is-finite32-p
      (frtv-memory-read memory-tag updates (frtv-shift base 3)))
     (frtv-is-finite32-p
      (frtv-memory-read memory-tag updates (frtv-shift base 4)))
     (frtv-is-finite32-p
      (frtv-memory-read memory-tag updates (frtv-shift base 5)))
     (frtv-is-finite32-p
      (frtv-memory-read memory-tag updates (frtv-shift base 6)))
     (frtv-is-finite32-p
      (frtv-memory-read memory-tag updates (frtv-shift base 7)))
     (frtv-is-finite32-p
      (frtv-memory-read memory-tag updates (frtv-shift base 8))))))

(defun frtv-rvalid-floatrmat-p
    (malloc-tag memory-tag updates address)
  (and
   (frtv-finite-floatrmat-p memory-tag updates address)
   (frtv-valid-rd-p malloc-tag address 9)))

;; Vectors and matrices unfold the source three-field and nine-field records.

(defun frtv-vector (x y z)
  (list x y z))

(defun frtv-vector-x (vector)
  (car vector))

(defun frtv-vector-y (vector)
  (cadr vector))

(defun frtv-vector-z (vector)
  (caddr vector))

(defun frtv-vector-of-memory (memory-tag updates address)
  (frtv-vector
   (frtv-memory-read memory-tag updates (frtv-shift address 0))
   (frtv-memory-read memory-tag updates (frtv-shift address 1))
   (frtv-memory-read memory-tag updates (frtv-shift address 2))))

(defun frtv-matrix
    (a00 a01 a02 a10 a11 a12 a20 a21 a22)
  (list a00 a01 a02 a10 a11 a12 a20 a21 a22))

(defun frtv-matrix-entry (matrix row column)
  (nth (+ (* 3 row) column) matrix))

(defun frtv-matrix-of-memory (memory-tag updates address)
  (let ((base (frtv-shift address 0)))
    (frtv-matrix
     (frtv-memory-read memory-tag updates (frtv-shift base 0))
     (frtv-memory-read memory-tag updates (frtv-shift base 1))
     (frtv-memory-read memory-tag updates (frtv-shift base 2))
     (frtv-memory-read memory-tag updates (frtv-shift base 3))
     (frtv-memory-read memory-tag updates (frtv-shift base 4))
     (frtv-memory-read memory-tag updates (frtv-shift base 5))
     (frtv-memory-read memory-tag updates (frtv-shift base 6))
     (frtv-memory-read memory-tag updates (frtv-shift base 7))
     (frtv-memory-read memory-tag updates (frtv-shift base 8)))))

(defun frtv-matrix-vector-multiply (matrix vector)
  (frtv-vector
   (frtv-dot3
    (frtv-matrix-entry matrix 0 0) (frtv-vector-x vector)
    (frtv-matrix-entry matrix 0 1) (frtv-vector-y vector)
    (frtv-matrix-entry matrix 0 2) (frtv-vector-z vector))
   (frtv-dot3
    (frtv-matrix-entry matrix 1 0) (frtv-vector-x vector)
    (frtv-matrix-entry matrix 1 1) (frtv-vector-y vector)
    (frtv-matrix-entry matrix 1 2) (frtv-vector-z vector))
   (frtv-dot3
    (frtv-matrix-entry matrix 2 0) (frtv-vector-x vector)
    (frtv-matrix-entry matrix 2 1) (frtv-vector-y vector)
    (frtv-matrix-entry matrix 2 2) (frtv-vector-z vector))))

(defun frtv-vector-equal-p (left right)
  (and
   (equal (frtv-vector-x left) (frtv-vector-x right))
   (equal (frtv-vector-y left) (frtv-vector-y right))
   (equal (frtv-vector-z left) (frtv-vector-z right))))

(defun-sk
    ntp4vc-float-rmat-vmult-post-goal0-statement ()
  (forall
   (vector-input matrix-input destination memory-tag malloc-tag)
   (implies
    (and
     (frtv-address-p vector-input)
     (frtv-address-p matrix-input)
     (frtv-address-p destination)
     (frtv-malloc-function-p malloc-tag)
     (frtv-region-function-p))
    (let*
        ((a-3 (frtv-shift vector-input 0))
         (r (frtv-memory-read memory-tag nil a-3))
         (a-4 (frtv-shift vector-input 1))
         (r-1 (frtv-memory-read memory-tag nil a-4))
         (a-5 (frtv-shift vector-input 2))
         (r-2 (frtv-memory-read memory-tag nil a-5))
         (a-6 (frtv-shift matrix-input 0))
         (r-3
          (frtv-memory-read memory-tag nil (frtv-shift a-6 0)))
         (r-4
          (frtv-memory-read memory-tag nil (frtv-shift a-6 1)))
         (r-5
          (frtv-memory-read memory-tag nil (frtv-shift a-6 2)))
         (updates-1
          (frtv-memory-write
           nil
           (frtv-shift destination 0)
           (frtv-dot3 r-3 r r-4 r-1 r-5 r-2)))
         (r-6 (frtv-memory-read memory-tag updates-1 a-3))
         (r-7 (frtv-memory-read memory-tag updates-1 a-4))
         (r-8 (frtv-memory-read memory-tag updates-1 a-5))
         (r-9
          (frtv-memory-read
           memory-tag updates-1 (frtv-shift a-6 3)))
         (r-10
          (frtv-memory-read
           memory-tag updates-1 (frtv-shift a-6 4)))
         (r-11
          (frtv-memory-read
           memory-tag updates-1 (frtv-shift a-6 5)))
         (updates-2
          (frtv-memory-write
           updates-1
           (frtv-shift destination 1)
           (frtv-dot3 r-9 r-6 r-10 r-7 r-11 r-8)))
         (r-12 (frtv-memory-read memory-tag updates-2 a-3))
         (r-13 (frtv-memory-read memory-tag updates-2 a-4))
         (r-14 (frtv-memory-read memory-tag updates-2 a-5))
         (r-15
          (frtv-memory-read
           memory-tag updates-2 (frtv-shift a-6 6)))
         (r-16
          (frtv-memory-read
           memory-tag updates-2 (frtv-shift a-6 7)))
         (r-17
          (frtv-memory-read
           memory-tag updates-2 (frtv-shift a-6 8)))
         (updates-3
          (frtv-memory-write
           updates-2
           (frtv-shift destination 2)
           (frtv-dot3 r-15 r-12 r-16 r-13 r-17 r-14))))
      (implies
       (and
        (<= (frtv-region-op (frtv-address-base destination)) 0)
        (<= (frtv-region-op (frtv-address-base vector-input)) 0)
        (<= (frtv-region-op (frtv-address-base matrix-input)) 0)
        (frtv-linked-p malloc-tag)
        (frtv-valid-rw-p malloc-tag destination 3)
        (frtv-rvalid-floatvect3-p
         malloc-tag memory-tag nil vector-input)
        (frtv-rvalid-floatrmat-p
         malloc-tag memory-tag nil matrix-input)
        (frtv-separated-p destination 3 vector-input 3)
        (frtv-separated-p destination 3 matrix-input 9)
        (frtv-separated-p vector-input 3 matrix-input 9)
        (frtv-is-float32-p r)
        (frtv-is-float32-p r-1)
        (frtv-is-float32-p r-2)
        (frtv-is-float32-p r-3)
        (frtv-is-float32-p r-4)
        (frtv-is-float32-p r-5)
        (frtv-is-float32-p r-6)
        (frtv-is-float32-p r-7)
        (frtv-is-float32-p r-8)
        (frtv-is-float32-p r-9)
        (frtv-is-float32-p r-10)
        (frtv-is-float32-p r-11)
        (frtv-is-float32-p r-12)
        (frtv-is-float32-p r-13)
        (frtv-is-float32-p r-14)
        (frtv-is-float32-p r-15)
        (frtv-is-float32-p r-16)
        (frtv-is-float32-p r-17))
       (frtv-vector-equal-p
        (frtv-vector-of-memory memory-tag updates-3 destination)
        (frtv-matrix-vector-multiply
         (frtv-matrix-of-memory
          memory-tag updates-3 matrix-input)
         (frtv-vector-of-memory
          memory-tag updates-3 vector-input))))))))

(value-triple :itpeval-statement-checked)

:q
