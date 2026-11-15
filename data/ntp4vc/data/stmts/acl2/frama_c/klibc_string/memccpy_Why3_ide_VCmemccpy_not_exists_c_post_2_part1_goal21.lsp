;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/klibc_string/memccpy_Why3_ide_VCmemccpy_not_exists_c_post_2_part1_goal21:
;; equality of source and destination memory reads after a havoced integer
;; memory is functionally updated, under the stated bounds, memory validity,
;; separation, address-order, linkedness, constancy, and universally quantified
;; exclusion and copied-prefix hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mcc21-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mcc21-address-base (address)
  (car address))

(defun mcc21-address-offset (address)
  (cdr address))

(defun mcc21-shift (address amount)
  (cons
   (mcc21-address-base address)
   (+ (mcc21-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memories t_1 and t_2, allocation map t, region function, address
;; order, signed-byte conversion, and the linked and sconst predicates
;; specialized respectively to t and t_2.

(defstub mcc21-t1 (address) t)
(defstub mcc21-t2 (address) t)
(defstub mcc21-allocation (index) t)
(defstub mcc21-region (base) t)
(defstub mcc21-addr-le-op (left right) t)
(defstub mcc21-to-sint8 (value) t)
(defstub mcc21-linked-op () t)
(defstub mcc21-sconst-op () t)

(defun-sk mcc21-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (mcc21-address-p address)
      (and
       (integerp (mcc21-t1 address))
       (integerp (mcc21-t2 address))))
     (implies
      (integerp index)
      (integerp (mcc21-allocation index)))
     (implies
      (integerp base)
      (integerp (mcc21-region base)))
     (implies
      (integerp value)
      (integerp (mcc21-to-sint8 value))))))

(defun mcc21-addr-le-p (left right)
  (if (mcc21-addr-le-op left right) t nil))

;; This is the exact source law for address order: for addresses with the same
;; base, addr_le is precisely integer order on offsets.

(defun-sk mcc21-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (mcc21-address-p left)
      (mcc21-address-p right)
      (equal
       (mcc21-address-base left)
       (mcc21-address-base right)))
     (equal
      (mcc21-addr-le-p left right)
      (<=
       (mcc21-address-offset left)
       (mcc21-address-offset right))))))

(defun mcc21-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

;; This is Cint.id_sint8, the imported source law relevant to the bounded i_3.

(defun-sk mcc21-cint-law-p ()
  (forall (value)
    (implies
     (mcc21-is-sint8-p value)
     (equal (mcc21-to-sint8 value) value))))

(defun mcc21-linked-p ()
  (if (mcc21-linked-op) t nil))

(defun mcc21-sconst-p ()
  (if (mcc21-sconst-op) t nil))

(defun mcc21-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mcc21-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun mcc21-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mcc21-address-base address))
    (<= 0 (mcc21-address-offset address))
    (<=
     (+ (mcc21-address-offset address) length)
     (mcc21-allocation (mcc21-address-base address))))))

(defun mcc21-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mcc21-address-base left)
     (mcc21-address-base right)))
   (<=
    (+ (mcc21-address-offset right) right-length)
    (mcc21-address-offset left))
   (<=
    (+ (mcc21-address-offset left) left-length)
    (mcc21-address-offset right))))

;; Exact pointwise content of Memory.havoc_access for havoc t_1 t_2 a_2 x.

(defun mcc21-a3-read (address a1 i1 i)
  (let*
      ((a2 (mcc21-shift a1 0))
       (x (- i1 i)))
    (if (mcc21-separated-p address 1 a2 x)
        (mcc21-t2 address)
      (mcc21-t1 address))))

;; Exact functional update a_3(a_7 := a_5), including address aliasing.

(defun mcc21-a8-read (address a a1 i1 i)
  (let*
      ((x (- i1 i))
       (a4 (mcc21-shift a x))
       (a5 (mcc21-a3-read a4 a1 i1 i))
       (a7 (mcc21-shift a1 x)))
    (if (equal address a7)
        a5
      (mcc21-a3-read address a1 i1 i))))

;; The three source hypotheses remain universally quantified over every
;; mathematical integer i_4.

(defun-sk mcc21-a3-prefix-equal-p (a a1 i1 i)
  (forall (i4)
    (implies
     (integerp i4)
     (implies
      (and
       (<= 0 i4)
       (< (+ i4 i) i1))
      (equal
       (mcc21-a3-read (mcc21-shift a1 i4) a1 i1 i)
       (mcc21-a3-read (mcc21-shift a i4) a1 i1 i))))))

(defun-sk mcc21-t2-excludes-a5-p (a a1 i1 i)
  (forall (i4)
    (implies
     (integerp i4)
     (implies
      (and
       (<= 0 i4)
       (< i4 i1))
      (not
       (equal
        (mcc21-a3-read
         (mcc21-shift a (- i1 i)) a1 i1 i)
        (mcc21-t2 (mcc21-shift a i4))))))))

(defun-sk mcc21-a3-excludes-a5-p (a a1 i1 i)
  (forall (i4)
    (implies
     (integerp i4)
     (implies
      (and
       (<= 0 i4)
       (< (+ i4 i) i1))
      (not
       (equal
        (mcc21-a3-read
         (mcc21-shift a (- i1 i)) a1 i1 i)
        (mcc21-a3-read
         (mcc21-shift a1 i4) a1 i1 i)))))))

(defun-sk
    ntp4vc-memccpy-not-exists-c-post-2-part1-goal21-statement ()
  (forall
   (a1 i1 i a i3 i2)
   (implies
    (and
     (mcc21-address-p a1)
     (integerp i1)
     (integerp i)
     (mcc21-address-p a)
     (integerp i3)
     (integerp i2)
     (mcc21-function-types-p)
     (mcc21-address-order-law-p)
     (mcc21-cint-law-p))
    (let*
        ((a2 (mcc21-shift a1 0))
         (x (- i1 i))
         (a4 (mcc21-shift a x))
         (a5 (mcc21-a3-read a4 a1 i1 i))
         (a6 (mcc21-shift a 0))
         (a7 (mcc21-shift a1 x)))
      (implies
       (and
        (not (equal i 0))
        (equal a5 (mcc21-to-sint8 i3))
        (< 0 i1)
        (<= 0 i)
        (<= i i1)
        (<= 0 i2)
        (< i2 i1)
        (<= (mcc21-region (mcc21-address-base a)) 0)
        (<= (mcc21-region (mcc21-address-base a1)) 0)
        (<= -128 i3)
        (<= i3 127)
        (mcc21-linked-p)
        (mcc21-sconst-p)
        (mcc21-is-uint32-p i)
        (mcc21-is-uint32-p i1)
        (mcc21-is-sint32-p i3)
        (mcc21-valid-rw-p a6 i1)
        (mcc21-valid-rw-p a2 i1)
        (mcc21-separated-p a6 i1 a2 i1)
        (mcc21-addr-le-p a a4)
        (mcc21-addr-le-p a1 a7)
        (mcc21-addr-le-p a4 (mcc21-shift a i1))
        (mcc21-addr-le-p a7 (mcc21-shift a1 i1))
        (mcc21-a3-prefix-equal-p a a1 i1 i)
        (mcc21-t2-excludes-a5-p a a1 i1 i)
        (mcc21-a3-excludes-a5-p a a1 i1 i))
       (equal
        (mcc21-a8-read (mcc21-shift a1 i2) a a1 i1 i)
        (mcc21-a8-read (mcc21-shift a i2) a a1 i1 i)))))))

(value-triple :itpeval-statement-checked)

:q
