;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/klibc_string/memccpy_Why3_ide_VCmemccpy_loop_inv_7_preserved_goal12:
;; preservation of equality between the source and destination memory reads
;; after one functional memory update, under the stated byte bounds, memory
;; validity, separation, address-order, linkedness, constancy, and universally
;; quantified prefix invariants. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mcc12-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mcc12-address-base (address)
  (car address))

(defun mcc12-address-offset (address)
  (cdr address))

(defun mcc12-shift (address amount)
  (cons
   (mcc12-address-base address)
   (+ (mcc12-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memories t_1 and t_2, allocation map t, region function, address
;; order, integer conversions, and the linked and sconst predicates specialized
;; respectively to t and t_2.

(defstub mcc12-t1 (address) t)
(defstub mcc12-t2 (address) t)
(defstub mcc12-allocation (index) t)
(defstub mcc12-region (base) t)
(defstub mcc12-addr-le-op (left right) t)
(defstub mcc12-to-sint8 (value) t)
(defstub mcc12-to-uint32 (value) t)
(defstub mcc12-linked-op () t)
(defstub mcc12-sconst-op () t)

(defun-sk mcc12-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (mcc12-address-p address)
      (and
       (integerp (mcc12-t1 address))
       (integerp (mcc12-t2 address))))
     (implies
      (integerp index)
      (integerp (mcc12-allocation index)))
     (implies
      (integerp base)
      (integerp (mcc12-region base)))
     (implies
      (integerp value)
      (and
       (integerp (mcc12-to-sint8 value))
       (integerp (mcc12-to-uint32 value)))))))

(defun mcc12-addr-le-p (left right)
  (if (mcc12-addr-le-op left right) t nil))

;; This is the exact source law for address order: for addresses with the same
;; base, addr_le is precisely integer order on offsets.

(defun-sk mcc12-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (mcc12-address-p left)
      (mcc12-address-p right)
      (equal
       (mcc12-address-base left)
       (mcc12-address-base right)))
     (equal
      (mcc12-addr-le-p left right)
      (<=
       (mcc12-address-offset left)
       (mcc12-address-offset right))))))

(defun mcc12-linked-p ()
  (if (mcc12-linked-op) t nil))

(defun mcc12-sconst-p ()
  (if (mcc12-sconst-op) t nil))

(defun mcc12-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun mcc12-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mcc12-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; These are the imported Cint identity laws relevant to the bounded
;; conversion arguments in this verification condition.

(defun-sk mcc12-cint-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (implies
       (mcc12-is-sint8-p value)
       (equal (mcc12-to-sint8 value) value))
      (implies
       (mcc12-is-uint32-p value)
       (equal (mcc12-to-uint32 value) value))))))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun mcc12-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mcc12-address-base address))
    (<= 0 (mcc12-address-offset address))
    (<=
     (+ (mcc12-address-offset address) length)
     (mcc12-allocation (mcc12-address-base address))))))

(defun mcc12-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mcc12-address-base left)
     (mcc12-address-base right)))
   (<=
    (+ (mcc12-address-offset right) right-length)
    (mcc12-address-offset left))
   (<=
    (+ (mcc12-address-offset left) left-length)
    (mcc12-address-offset right))))

;; Exact pointwise content of Memory.havoc_access for havoc t_1 t_2 a_2 x.

(defun mcc12-a3-read (address a1 i1 i)
  (let*
      ((a2 (mcc12-shift a1 0))
       (x (- i1 i)))
    (if (mcc12-separated-p address 1 a2 x)
        (mcc12-t2 address)
      (mcc12-t1 address))))

;; Exact functional update a_3(a_7 := a_5), including address aliasing.

(defun mcc12-a8-read (address a a1 i1 i)
  (let*
      ((x (- i1 i))
       (a4 (mcc12-shift a x))
       (a5 (mcc12-a3-read a4 a1 i1 i))
       (a7 (mcc12-shift a1 x)))
    (if (equal address a7)
        a5
      (mcc12-a3-read address a1 i1 i))))

;; The two source loop-invariant hypotheses remain universally quantified over
;; every mathematical integer i_4.

(defun-sk mcc12-a3-prefix-equal-p (a a1 i1 i)
  (forall (i4)
    (implies
     (integerp i4)
     (implies
      (and
       (<= 0 i4)
       (< (+ i4 i) i1))
      (equal
       (mcc12-a3-read (mcc12-shift a1 i4) a1 i1 i)
       (mcc12-a3-read (mcc12-shift a i4) a1 i1 i))))))

(defun-sk mcc12-a3-prefix-excludes-p (a a1 i3 i1 i)
  (forall (i4)
    (implies
     (integerp i4)
     (implies
      (and
       (<= 0 i4)
       (< (+ i4 i) i1))
      (not
       (equal
        (mcc12-a3-read (mcc12-shift a1 i4) a1 i1 i)
        (mcc12-to-sint8 i3)))))))

(defun-sk
    ntp4vc-memccpy-loop-inv-7-preserved-goal12-statement ()
  (forall
   (a1 i1 i a i3 i2)
   (implies
    (and
     (mcc12-address-p a1)
     (integerp i1)
     (integerp i)
     (mcc12-address-p a)
     (integerp i3)
     (integerp i2)
     (mcc12-function-types-p)
     (mcc12-address-order-law-p)
     (mcc12-cint-laws-p))
    (let*
        ((a2 (mcc12-shift a1 0))
         (x (- i1 i))
         (a4 (mcc12-shift a x))
         (a5 (mcc12-a3-read a4 a1 i1 i))
         (x1 (mcc12-to-sint8 i3))
         (a6 (mcc12-shift a 0))
         (a7 (mcc12-shift a1 x)))
      (implies
       (and
        (not (equal i 0))
        (not (equal a5 x1))
        (< 0 i1)
        (<= 0 i)
        (<= i i1)
        (<= 0 i2)
        (<= (mcc12-region (mcc12-address-base a)) 0)
        (<= (mcc12-region (mcc12-address-base a1)) 0)
        (< (+ i2 (mcc12-to-uint32 (- i 1))) i1)
        (<= -128 i3)
        (<= i3 127)
        (mcc12-linked-p)
        (mcc12-sconst-p)
        (mcc12-is-uint32-p i)
        (mcc12-is-uint32-p i1)
        (mcc12-is-sint32-p i3)
        (mcc12-valid-rw-p a6 i1)
        (mcc12-valid-rw-p a2 i1)
        (mcc12-separated-p a6 i1 a2 i1)
        (mcc12-addr-le-p a a4)
        (mcc12-addr-le-p a1 a7)
        (mcc12-addr-le-p a4 (mcc12-shift a i1))
        (mcc12-addr-le-p a7 (mcc12-shift a1 i1))
        (mcc12-is-sint8-p a5)
        (mcc12-a3-prefix-equal-p a a1 i1 i)
        (mcc12-a3-prefix-excludes-p a a1 i3 i1 i))
       (equal
        (mcc12-a8-read (mcc12-shift a1 i2) a a1 i1 i)
        (mcc12-a8-read (mcc12-shift a i2) a a1 i1 i)))))))

(value-triple :itpeval-statement-checked)

:q
