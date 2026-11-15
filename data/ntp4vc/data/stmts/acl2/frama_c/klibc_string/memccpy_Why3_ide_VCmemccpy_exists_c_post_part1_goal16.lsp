;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/klibc_string/memccpy_Why3_ide_VCmemccpy_exists_c_post_part1_goal16:
;; preservation of the copied-memory prefix and exclusion of the stopping byte
;; after one integer-memory update, under the stated bounds, memory validity,
;; separation, address-order, linkedness, and constancy hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mcc16-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mcc16-address-base (address)
  (car address))

(defun mcc16-address-offset (address)
  (cdr address))

(defun mcc16-shift (address amount)
  (cons
   (mcc16-address-base address)
   (+ (mcc16-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memories t_2 and t_1, allocation map t, region function, address
;; order, signed-byte conversion, and the linked and sconst predicates
;; specialized to t and t_2.

(defstub mcc16-t2 (address) t)
(defstub mcc16-t1 (address) t)
(defstub mcc16-allocation (index) t)
(defstub mcc16-region (base) t)
(defstub mcc16-addr-le-op (left right) t)
(defstub mcc16-to-sint8 (value) t)
(defstub mcc16-linked-op () t)
(defstub mcc16-sconst-op () t)

(defun-sk mcc16-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (mcc16-address-p address)
      (and
       (integerp (mcc16-t2 address))
       (integerp (mcc16-t1 address))))
     (implies
      (integerp index)
      (integerp (mcc16-allocation index)))
     (implies
      (integerp base)
      (integerp (mcc16-region base)))
     (implies
      (integerp value)
      (integerp (mcc16-to-sint8 value))))))

(defun mcc16-addr-le-p (left right)
  (if (mcc16-addr-le-op left right) t nil))

;; This is the exact source law for address order: for addresses with the same
;; base, addr_le is precisely integer order on offsets.

(defun-sk mcc16-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (mcc16-address-p left)
      (mcc16-address-p right)
      (equal
       (mcc16-address-base left)
       (mcc16-address-base right)))
     (equal
      (mcc16-addr-le-p left right)
      (<=
       (mcc16-address-offset left)
       (mcc16-address-offset right))))))

(defun mcc16-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

;; This is Cint.id_sint8, the imported source law relevant to the bounded i_3.

(defun-sk mcc16-cint-law-p ()
  (forall (value)
    (implies
     (mcc16-is-sint8-p value)
     (equal (mcc16-to-sint8 value) value))))

(defun mcc16-linked-p ()
  (if (mcc16-linked-op) t nil))

(defun mcc16-sconst-p ()
  (if (mcc16-sconst-op) t nil))

(defun mcc16-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun mcc16-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun mcc16-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mcc16-address-base address))
    (<= 0 (mcc16-address-offset address))
    (<=
     (+ (mcc16-address-offset address) length)
     (mcc16-allocation (mcc16-address-base address))))))

(defun mcc16-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mcc16-address-base left)
     (mcc16-address-base right)))
   (<=
    (+ (mcc16-address-offset right) right-length)
    (mcc16-address-offset left))
   (<=
    (+ (mcc16-address-offset left) left-length)
    (mcc16-address-offset right))))

;; This is the exact pointwise content of Memory.havoc_access for
;; havoc t_1 t_2 a_2 x_1.

(defun mcc16-a3-read (address a1 i1 i)
  (let*
      ((a2 (mcc16-shift a1 0))
       (x1 (- i1 i)))
    (if (mcc16-separated-p address 1 a2 x1)
        (mcc16-t2 address)
      (mcc16-t1 address))))

;; This is the exact functional update a_3(a_6 := x), including aliasing.

(defun mcc16-a7-read (address a a1 i2 i1 i)
  (let*
      ((x (mcc16-t2 (mcc16-shift a i2)))
       (x1 (- i1 i))
       (a6 (mcc16-shift a1 x1)))
    (if (equal address a6)
        x
      (mcc16-a3-read address a1 i1 i))))

;; The two source hypotheses quantified over every mathematical integer i_4.

(defun-sk mcc16-a3-prefix-equal-p (a a1 i1 i)
  (forall (i4)
    (implies
     (integerp i4)
     (implies
      (and
       (<= 0 i4)
       (< (+ i4 i) i1))
      (equal
       (mcc16-a3-read (mcc16-shift a1 i4) a1 i1 i)
       (mcc16-a3-read (mcc16-shift a i4) a1 i1 i))))))

(defun-sk mcc16-a3-prefix-excludes-p (a a1 i2 i1 i)
  (forall (i4)
    (implies
     (integerp i4)
     (implies
      (and
       (<= 0 i4)
       (< (+ i4 i) i1))
      (not
       (equal
        (mcc16-a3-read (mcc16-shift a1 i4) a1 i1 i)
        (mcc16-t2 (mcc16-shift a i2))))))))

;; The two source postconditions quantified over every mathematical integer
;; i_4 after the functional update.

(defun-sk mcc16-a7-prefix-equal-p (a a1 i2 i1 i)
  (forall (i4)
    (implies
     (integerp i4)
     (implies
      (and
       (<= 0 i4)
       (<= (+ i4 i) i1))
      (equal
       (mcc16-a7-read
        (mcc16-shift a1 i4) a a1 i2 i1 i)
       (mcc16-a7-read
        (mcc16-shift a i4) a a1 i2 i1 i))))))

(defun-sk mcc16-a7-prefix-excludes-p (a a1 i2 i1 i)
  (forall (i4)
    (implies
     (integerp i4)
     (implies
      (and
       (<= 0 i4)
       (< (+ i4 i) i1))
      (not
       (equal
        (mcc16-a7-read
         (mcc16-shift a i4) a a1 i2 i1 i)
        (mcc16-t2 (mcc16-shift a i2))))))))

(defun-sk ntp4vc-memccpy-exists-c-post-part1-goal16-statement ()
  (forall
   (a i2 a1 i1 i i3)
   (implies
    (and
     (mcc16-address-p a)
     (integerp i2)
     (mcc16-address-p a1)
     (integerp i1)
     (integerp i)
     (integerp i3)
     (mcc16-function-types-p)
     (mcc16-address-order-law-p)
     (mcc16-cint-law-p))
    (let*
        ((x (mcc16-t2 (mcc16-shift a i2)))
         (a2 (mcc16-shift a1 0))
         (x1 (- i1 i))
         (a4 (mcc16-shift a x1))
         (a5 (mcc16-shift a 0))
         (a6 (mcc16-shift a1 x1)))
      (implies
       (and
        (not (equal i 0))
        (equal x (mcc16-to-sint8 i3))
        (equal (mcc16-a3-read a4 a1 i1 i) x)
        (< 0 i1)
        (<= 0 i)
        (<= i i1)
        (<= 0 i2)
        (< i2 i1)
        (<= (mcc16-region (mcc16-address-base a)) 0)
        (<= (mcc16-region (mcc16-address-base a1)) 0)
        (<= -128 i3)
        (<= i3 127)
        (mcc16-linked-p)
        (mcc16-sconst-p)
        (mcc16-is-uint32-p i)
        (mcc16-is-uint32-p i1)
        (mcc16-is-sint32-p i3)
        (mcc16-valid-rw-p a5 i1)
        (mcc16-valid-rw-p a2 i1)
        (mcc16-separated-p a5 i1 a2 i1)
        (mcc16-addr-le-p a a4)
        (mcc16-addr-le-p a1 a6)
        (mcc16-addr-le-p a4 (mcc16-shift a i1))
        (mcc16-addr-le-p a6 (mcc16-shift a1 i1))
        (mcc16-a3-prefix-equal-p a a1 i1 i)
        (mcc16-a3-prefix-excludes-p a a1 i2 i1 i))
       (and
        (equal
         (mcc16-a7-read a4 a a1 i2 i1 i)
         x)
        (< 0 i)
        (mcc16-a7-prefix-equal-p a a1 i2 i1 i)
        (mcc16-a7-prefix-excludes-p a a1 i2 i1 i)))))))

(value-triple :itpeval-statement-checked)

:q
