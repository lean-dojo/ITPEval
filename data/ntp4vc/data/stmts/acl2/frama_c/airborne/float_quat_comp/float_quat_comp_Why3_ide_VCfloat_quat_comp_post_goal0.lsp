;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/airborne/float_quat_comp/float_quat_comp_Why3_ide_VCfloat_quat_comp_post_goal0:
;; in-place writes of the four real polynomial components of a quaternion
;; product yield the specified quaternion under the stated memory-validity and
;; non-aliasing conditions. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Addresses are exactly pairs of mathematical integers, matching the source
;; record with integer base and offset fields.

(defun float-quat-comp-address-p (address)
  (and (consp address)
       (integerp (car address))
       (integerp (cdr address))))

(defun float-quat-comp-address-base (address)
  (car address))

(defun float-quat-comp-address-offset (address)
  (cdr address))

(defun float-quat-comp-shift (address amount)
  (cons (float-quat-comp-address-base address)
        (+ (float-quat-comp-address-offset address) amount)))

;; These conservative interfaces represent the source's arbitrary allocation
;; function, region function, and linked-memory predicate. A tag identifies an
;; arbitrary source function without replacing it by a finite table.

(defstub float-quat-comp-malloc-at (malloc-tag index) t)
(defstub float-quat-comp-region (base) t)
(defstub float-quat-comp-linked-op (malloc-tag) t)

(defun float-quat-comp-linked-p (malloc-tag)
  (if (float-quat-comp-linked-op malloc-tag) t nil))

(defun-sk float-quat-comp-malloc-function-p (malloc-tag)
  (forall (index)
    (implies
     (integerp index)
     (integerp
      (float-quat-comp-malloc-at malloc-tag index)))))

(defun-sk float-quat-comp-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (float-quat-comp-region base)))))

(defun float-quat-comp-valid-rw-p
    (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (< 0 (float-quat-comp-address-base address))
    (<= 0 (float-quat-comp-address-offset address))
    (<= (+ (float-quat-comp-address-offset address) length)
        (float-quat-comp-malloc-at
         malloc-tag
         (float-quat-comp-address-base address))))))

(defun float-quat-comp-valid-rd-p
    (malloc-tag address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (float-quat-comp-address-base address)))
    (<= 0 (float-quat-comp-address-offset address))
    (<= (+ (float-quat-comp-address-offset address) length)
        (float-quat-comp-malloc-at
         malloc-tag
         (float-quat-comp-address-base address))))))

;; A polynomial is a canonical sorted list of
;; (sorted-monomial . integer-coefficient) pairs. Its variables are arbitrary
;; memory-cell names. Equality of these polynomials is equivalent to equality
;; under every assignment of real values to the cells, so this preserves the
;; source's universally quantified function addr -> real without restricting
;; real values to ACL2 rationals.

(defun float-quat-comp-monomial-multiply (left right)
  (declare
   (xargs
    :measure (+ (acl2-count left) (acl2-count right))))
  (cond
   ((endp left) right)
   ((endp right) left)
   ((lexorder (car left) (car right))
    (cons
     (car left)
     (float-quat-comp-monomial-multiply
      (cdr left) right)))
   (t
    (cons
     (car right)
     (float-quat-comp-monomial-multiply
      left (cdr right))))))

(defun float-quat-comp-polynomial-insert
    (monomial coefficient polynomial)
  (cond
   ((equal coefficient 0) polynomial)
   ((endp polynomial)
    (list (cons monomial coefficient)))
   ((equal monomial (caar polynomial))
    (let ((sum (+ coefficient (cdar polynomial))))
      (if (equal sum 0)
          (cdr polynomial)
        (cons
         (cons monomial sum)
         (cdr polynomial)))))
   ((lexorder monomial (caar polynomial))
    (cons (cons monomial coefficient) polynomial))
   (t
    (cons
     (car polynomial)
     (float-quat-comp-polynomial-insert
      monomial coefficient (cdr polynomial))))))

(defun float-quat-comp-polynomial-add (left right)
  (if (endp left)
      right
    (float-quat-comp-polynomial-add
     (cdr left)
     (float-quat-comp-polynomial-insert
      (caar left) (cdar left) right))))

(defun float-quat-comp-polynomial-negate (polynomial)
  (if (endp polynomial)
      nil
    (cons
     (cons (caar polynomial) (- (cdar polynomial)))
     (float-quat-comp-polynomial-negate
      (cdr polynomial)))))

(defun float-quat-comp-polynomial-multiply-term
    (monomial coefficient polynomial)
  (if (endp polynomial)
      nil
    (float-quat-comp-polynomial-insert
     (float-quat-comp-monomial-multiply
      monomial (caar polynomial))
     (* coefficient (cdar polynomial))
     (float-quat-comp-polynomial-multiply-term
      monomial coefficient (cdr polynomial)))))

(defun float-quat-comp-polynomial-multiply (left right)
  (if (endp left)
      nil
    (float-quat-comp-polynomial-add
     (float-quat-comp-polynomial-multiply-term
      (caar left) (cdar left) right)
     (float-quat-comp-polynomial-multiply
      (cdr left) right))))

(defun float-quat-comp-polynomial-variable (name)
  (list (cons (list name) 1)))

(defun float-quat-comp-r-add (left right)
  (float-quat-comp-polynomial-add left right))

(defun float-quat-comp-r-negate (value)
  (float-quat-comp-polynomial-negate value))

(defun float-quat-comp-r-multiply (left right)
  (float-quat-comp-polynomial-multiply left right))

(defun float-quat-comp-r-add4 (a b c d)
  (float-quat-comp-r-add
   (float-quat-comp-r-add
    (float-quat-comp-r-add a b)
    c)
   d))

;; An update list is newest first. Assoc-equal therefore gives exactly the
;; source's successive Function.update semantics, including address aliasing.

(defun float-quat-comp-memory-read
    (memory-tag updates address)
  (let ((entry (assoc-equal address updates)))
    (if entry
        (cdr entry)
      (float-quat-comp-polynomial-variable
       (list memory-tag address)))))

(defun float-quat-comp-memory-write
    (updates address value)
  (cons (cons address value) updates))

;; In the imported source theory is_float32 is definitionally True, and the
;; supplied classification axiom makes is_finite32 true for every real.

(defun float-quat-comp-is-float32-p (value)
  (declare (ignore value))
  t)

(defun float-quat-comp-is-finite32-p (value)
  (declare (ignore value))
  t)

(defun float-quat-comp-finite-floatquat-p
    (memory-tag updates address)
  (and
   (float-quat-comp-is-finite32-p
    (float-quat-comp-memory-read
     memory-tag updates
     (float-quat-comp-shift address 0)))
   (float-quat-comp-is-finite32-p
    (float-quat-comp-memory-read
     memory-tag updates
     (float-quat-comp-shift address 1)))
   (float-quat-comp-is-finite32-p
    (float-quat-comp-memory-read
     memory-tag updates
     (float-quat-comp-shift address 2)))
   (float-quat-comp-is-finite32-p
    (float-quat-comp-memory-read
     memory-tag updates
     (float-quat-comp-shift address 3)))))

(defun float-quat-comp-rvalid-floatquat-p
    (malloc-tag memory-tag updates address)
  (and
   (float-quat-comp-finite-floatquat-p
    memory-tag updates address)
   (float-quat-comp-valid-rd-p
    malloc-tag address 4)))

;; Quaternions are scalar/x/y/z tuples. The multiplication below unfolds the
;; exact dot-product, scalar multiplication, addition, and cross-product
;; definitions shared by the three ground-truth sources.

(defun float-quat-comp-quaternion
    (scalar x y z)
  (list scalar x y z))

(defun float-quat-comp-quaternion-scalar (quaternion)
  (car quaternion))

(defun float-quat-comp-quaternion-x (quaternion)
  (cadr quaternion))

(defun float-quat-comp-quaternion-y (quaternion)
  (caddr quaternion))

(defun float-quat-comp-quaternion-z (quaternion)
  (cadddr quaternion))

(defun float-quat-comp-quaternion-of-memory
    (memory-tag updates address)
  (float-quat-comp-quaternion
   (float-quat-comp-memory-read
    memory-tag updates
    (float-quat-comp-shift address 0))
   (float-quat-comp-memory-read
    memory-tag updates
    (float-quat-comp-shift address 1))
   (float-quat-comp-memory-read
    memory-tag updates
    (float-quat-comp-shift address 2))
   (float-quat-comp-memory-read
    memory-tag updates
    (float-quat-comp-shift address 3))))

(defun float-quat-comp-quaternion-multiply (left right)
  (let*
      ((left-s
        (float-quat-comp-quaternion-scalar left))
       (left-x
        (float-quat-comp-quaternion-x left))
       (left-y
        (float-quat-comp-quaternion-y left))
       (left-z
        (float-quat-comp-quaternion-z left))
       (right-s
        (float-quat-comp-quaternion-scalar right))
       (right-x
        (float-quat-comp-quaternion-x right))
       (right-y
        (float-quat-comp-quaternion-y right))
       (right-z
        (float-quat-comp-quaternion-z right)))
    (float-quat-comp-quaternion
     (float-quat-comp-r-add4
      (float-quat-comp-r-multiply left-s right-s)
      (float-quat-comp-r-negate
       (float-quat-comp-r-multiply left-x right-x))
      (float-quat-comp-r-negate
       (float-quat-comp-r-multiply left-y right-y))
      (float-quat-comp-r-negate
       (float-quat-comp-r-multiply left-z right-z)))
     (float-quat-comp-r-add4
      (float-quat-comp-r-multiply left-s right-x)
      (float-quat-comp-r-multiply right-s left-x)
      (float-quat-comp-r-multiply left-y right-z)
      (float-quat-comp-r-negate
       (float-quat-comp-r-multiply left-z right-y)))
     (float-quat-comp-r-add4
      (float-quat-comp-r-multiply left-s right-y)
      (float-quat-comp-r-multiply right-s left-y)
      (float-quat-comp-r-multiply left-z right-x)
      (float-quat-comp-r-negate
       (float-quat-comp-r-multiply left-x right-z)))
     (float-quat-comp-r-add4
      (float-quat-comp-r-multiply left-s right-z)
      (float-quat-comp-r-multiply right-s left-z)
      (float-quat-comp-r-multiply left-x right-y)
      (float-quat-comp-r-negate
       (float-quat-comp-r-multiply left-y right-x))))))

(defun float-quat-comp-quaternion-equal-p (left right)
  (and
   (equal
    (float-quat-comp-quaternion-scalar left)
    (float-quat-comp-quaternion-scalar right))
   (equal
    (float-quat-comp-quaternion-x left)
    (float-quat-comp-quaternion-x right))
   (equal
    (float-quat-comp-quaternion-y left)
    (float-quat-comp-quaternion-y right))
   (equal
    (float-quat-comp-quaternion-z left)
    (float-quat-comp-quaternion-z right))))

(defun float-quat-comp-distinct-addresses-p
    (a-3 a-4 a-5 a-6 a-7 a-8 a-9 a-10 a-11 a-12 a-13 a-14)
  (and
   (not (equal a-3 a-4))
   (not (equal a-5 a-4))
   (not (equal a-5 a-3))
   (not (equal a-6 a-3))
   (not (equal a-6 a-5))
   (not (equal a-7 a-4))
   (not (equal a-7 a-5))
   (not (equal a-7 a-6))
   (not (equal a-8 a-4))
   (not (equal a-8 a-3))
   (not (equal a-8 a-6))
   (not (equal a-8 a-7))
   (not (equal a-9 a-3))
   (not (equal a-9 a-5))
   (not (equal a-9 a-7))
   (not (equal a-9 a-8))
   (not (equal a-10 a-4))
   (not (equal a-10 a-5))
   (not (equal a-10 a-6))
   (not (equal a-10 a-8))
   (not (equal a-10 a-9))
   (not (equal a-11 a-4))
   (not (equal a-11 a-3))
   (not (equal a-11 a-6))
   (not (equal a-11 a-7))
   (not (equal a-11 a-9))
   (not (equal a-11 a-10))
   (not (equal a-12 a-3))
   (not (equal a-12 a-5))
   (not (equal a-12 a-7))
   (not (equal a-12 a-8))
   (not (equal a-12 a-10))
   (not (equal a-12 a-11))
   (not (equal a-13 a-4))
   (not (equal a-13 a-5))
   (not (equal a-13 a-6))
   (not (equal a-13 a-8))
   (not (equal a-13 a-9))
   (not (equal a-13 a-11))
   (not (equal a-13 a-12))
   (not (equal a-14 a-4))
   (not (equal a-14 a-3))
   (not (equal a-14 a-6))
   (not (equal a-14 a-7))
   (not (equal a-14 a-9))
   (not (equal a-14 a-10))
   (not (equal a-14 a-12))
   (not (equal a-14 a-13))))

(defun-sk
    ntp4vc-float-quat-comp-post-goal0-statement ()
  (forall
   (destination left-input right-input memory-tag malloc-tag)
   (implies
    (and
     (float-quat-comp-address-p destination)
     (float-quat-comp-address-p left-input)
     (float-quat-comp-address-p right-input)
     (float-quat-comp-region-function-p)
     (float-quat-comp-malloc-function-p malloc-tag))
    (let*
        ((a-3
          (float-quat-comp-shift destination 0))
         (a-4
          (float-quat-comp-shift left-input 0))
         (a-5
          (float-quat-comp-shift right-input 0))
         (a-6
          (float-quat-comp-shift left-input 1))
         (a-7
          (float-quat-comp-shift destination 1))
         (a-8
          (float-quat-comp-shift right-input 1))
         (a-9
          (float-quat-comp-shift left-input 2))
         (a-10
          (float-quat-comp-shift destination 2))
         (a-11
          (float-quat-comp-shift right-input 2))
         (a-12
          (float-quat-comp-shift left-input 3))
         (a-13
          (float-quat-comp-shift destination 3))
         (a-14
          (float-quat-comp-shift right-input 3))
         (updates-0 nil)
         (r
          (float-quat-comp-memory-read
           memory-tag updates-0 a-4))
         (r-1
          (float-quat-comp-memory-read
           memory-tag updates-0 a-5))
         (r-2
          (float-quat-comp-memory-read
           memory-tag updates-0 a-6))
         (r-3
          (float-quat-comp-memory-read
           memory-tag updates-0 a-8))
         (r-4
          (float-quat-comp-memory-read
           memory-tag updates-0 a-9))
         (r-5
          (float-quat-comp-memory-read
           memory-tag updates-0 a-11))
         (r-6
          (float-quat-comp-memory-read
           memory-tag updates-0 a-12))
         (r-7
          (float-quat-comp-memory-read
           memory-tag updates-0 a-14))
         (updates-1
          (float-quat-comp-memory-write
           updates-0
           a-3
           (float-quat-comp-r-add4
            (float-quat-comp-r-multiply r-1 r)
            (float-quat-comp-r-negate
             (float-quat-comp-r-multiply r-3 r-2))
            (float-quat-comp-r-negate
             (float-quat-comp-r-multiply r-5 r-4))
            (float-quat-comp-r-negate
             (float-quat-comp-r-multiply r-7 r-6)))))
         (r-8
          (float-quat-comp-memory-read
           memory-tag updates-1 a-4))
         (r-9
          (float-quat-comp-memory-read
           memory-tag updates-1 a-5))
         (r-10
          (float-quat-comp-memory-read
           memory-tag updates-1 a-6))
         (r-11
          (float-quat-comp-memory-read
           memory-tag updates-1 a-8))
         (r-12
          (float-quat-comp-memory-read
           memory-tag updates-1 a-9))
         (r-13
          (float-quat-comp-memory-read
           memory-tag updates-1 a-11))
         (r-14
          (float-quat-comp-memory-read
           memory-tag updates-1 a-12))
         (r-15
          (float-quat-comp-memory-read
           memory-tag updates-1 a-14))
         (updates-2
          (float-quat-comp-memory-write
           updates-1
           a-7
           (float-quat-comp-r-add4
            (float-quat-comp-r-multiply r-9 r-10)
            (float-quat-comp-r-multiply r-11 r-8)
            (float-quat-comp-r-multiply r-13 r-14)
            (float-quat-comp-r-negate
             (float-quat-comp-r-multiply r-15 r-12)))))
         (r-16
          (float-quat-comp-memory-read
           memory-tag updates-2 a-4))
         (r-17
          (float-quat-comp-memory-read
           memory-tag updates-2 a-5))
         (r-18
          (float-quat-comp-memory-read
           memory-tag updates-2 a-6))
         (r-19
          (float-quat-comp-memory-read
           memory-tag updates-2 a-8))
         (r-20
          (float-quat-comp-memory-read
           memory-tag updates-2 a-9))
         (r-21
          (float-quat-comp-memory-read
           memory-tag updates-2 a-11))
         (r-22
          (float-quat-comp-memory-read
           memory-tag updates-2 a-12))
         (r-23
          (float-quat-comp-memory-read
           memory-tag updates-2 a-14))
         (updates-3
          (float-quat-comp-memory-write
           updates-2
           a-10
           (float-quat-comp-r-add4
            (float-quat-comp-r-multiply r-17 r-20)
            (float-quat-comp-r-negate
             (float-quat-comp-r-multiply r-19 r-22))
            (float-quat-comp-r-multiply r-21 r-16)
            (float-quat-comp-r-multiply r-23 r-18))))
         (r-24
          (float-quat-comp-memory-read
           memory-tag updates-3 a-4))
         (r-25
          (float-quat-comp-memory-read
           memory-tag updates-3 a-5))
         (r-26
          (float-quat-comp-memory-read
           memory-tag updates-3 a-6))
         (r-27
          (float-quat-comp-memory-read
           memory-tag updates-3 a-8))
         (r-28
          (float-quat-comp-memory-read
           memory-tag updates-3 a-9))
         (r-29
          (float-quat-comp-memory-read
           memory-tag updates-3 a-11))
         (r-30
          (float-quat-comp-memory-read
           memory-tag updates-3 a-12))
         (r-31
          (float-quat-comp-memory-read
           memory-tag updates-3 a-14))
         (updates-4
          (float-quat-comp-memory-write
           updates-3
           a-13
           (float-quat-comp-r-add4
            (float-quat-comp-r-multiply r-25 r-30)
            (float-quat-comp-r-multiply r-27 r-28)
            (float-quat-comp-r-negate
             (float-quat-comp-r-multiply r-29 r-26))
            (float-quat-comp-r-multiply r-31 r-24)))))
      (implies
       (and
        (float-quat-comp-distinct-addresses-p
         a-3 a-4 a-5 a-6 a-7 a-8 a-9
         a-10 a-11 a-12 a-13 a-14)
        (<=
         (float-quat-comp-region
          (float-quat-comp-address-base left-input))
         0)
        (<=
         (float-quat-comp-region
          (float-quat-comp-address-base destination))
         0)
        (<=
         (float-quat-comp-region
          (float-quat-comp-address-base right-input))
         0)
        (float-quat-comp-linked-p malloc-tag)
        (float-quat-comp-valid-rw-p
         malloc-tag destination 4)
        (float-quat-comp-rvalid-floatquat-p
         malloc-tag memory-tag updates-0 left-input)
        (float-quat-comp-rvalid-floatquat-p
         malloc-tag memory-tag updates-0 right-input)
        (float-quat-comp-is-float32-p r)
        (float-quat-comp-is-float32-p r-1)
        (float-quat-comp-is-float32-p r-2)
        (float-quat-comp-is-float32-p r-3)
        (float-quat-comp-is-float32-p r-4)
        (float-quat-comp-is-float32-p r-5)
        (float-quat-comp-is-float32-p r-6)
        (float-quat-comp-is-float32-p r-7)
        (float-quat-comp-is-float32-p r-8)
        (float-quat-comp-is-float32-p r-9)
        (float-quat-comp-is-float32-p r-10)
        (float-quat-comp-is-float32-p r-11)
        (float-quat-comp-is-float32-p r-12)
        (float-quat-comp-is-float32-p r-13)
        (float-quat-comp-is-float32-p r-14)
        (float-quat-comp-is-float32-p r-15)
        (float-quat-comp-is-float32-p r-16)
        (float-quat-comp-is-float32-p r-17)
        (float-quat-comp-is-float32-p r-18)
        (float-quat-comp-is-float32-p r-19)
        (float-quat-comp-is-float32-p r-20)
        (float-quat-comp-is-float32-p r-21)
        (float-quat-comp-is-float32-p r-22)
        (float-quat-comp-is-float32-p r-23)
        (float-quat-comp-is-float32-p r-24)
        (float-quat-comp-is-float32-p r-25)
        (float-quat-comp-is-float32-p r-26)
        (float-quat-comp-is-float32-p r-27)
        (float-quat-comp-is-float32-p r-28)
        (float-quat-comp-is-float32-p r-29)
        (float-quat-comp-is-float32-p r-30)
        (float-quat-comp-is-float32-p r-31))
       (float-quat-comp-quaternion-equal-p
        (float-quat-comp-quaternion-of-memory
         memory-tag updates-4 destination)
        (float-quat-comp-quaternion-multiply
         (float-quat-comp-quaternion-of-memory
          memory-tag updates-4 right-input)
         (float-quat-comp-quaternion-of-memory
          memory-tag updates-4 left-input))))))))

(value-triple :itpeval-statement-checked)
:q
