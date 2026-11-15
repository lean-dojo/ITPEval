;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchrnul_Why3_ide_VCstrchrnul_assert_2_goal8:
;; the logical length of a valid C string reaches the current null-byte
;; address, under the stated strchrnul equality, address-order, memory-validity,
;; linkedness, constancy, and no-earlier-match hypotheses. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sng8-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sng8-address-base (address)
  (car address))

(defun sng8-address-offset (address)
  (cdr address))

(defun sng8-shift (address amount)
  (cons
   (sng8-address-base address)
   (+ (sng8-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchrnul, C integer conversion,
;; linkedness, and constancy symbols.

(defstub sng8-character-memory (address) t)
(defstub sng8-allocation (index) t)
(defstub sng8-region (base) t)
(defstub sng8-addr-le-op (left right) t)
(defstub sng8-addr-lt-op (left right) t)
(defstub sng8-l-strlen (address) t)
(defstub sng8-l-strchrnul (address value) t)
(defstub sng8-to-sint8 (value) t)
(defstub sng8-to-uint64 (value) t)
(defstub sng8-linked-op () t)
(defstub sng8-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sng8-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (sng8-address-p address)
      (and
       (integerp
        (sng8-character-memory address))
       (integerp
        (sng8-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (sng8-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sng8-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (sng8-to-sint8 value))
       (integerp
        (sng8-to-uint64 value))))
     (implies
      (and
       (sng8-address-p address)
       (integerp value))
      (sng8-address-p
       (sng8-l-strchrnul address value))))))

(defun sng8-addr-le-p (left right)
  (if (sng8-addr-le-op left right) t nil))

(defun sng8-addr-lt-p (left right)
  (if (sng8-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; integer order on offsets.

(defun-sk sng8-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (sng8-address-p left)
      (sng8-address-p right)
      (equal
       (sng8-address-base left)
       (sng8-address-base right)))
     (and
      (equal
       (sng8-addr-le-p left right)
       (<=
        (sng8-address-offset left)
        (sng8-address-offset right)))
      (equal
       (sng8-addr-lt-p left right)
       (<
        (sng8-address-offset left)
        (sng8-address-offset right)))))))

(defun sng8-linked-p ()
  (if (sng8-linked-op) t nil))

(defun sng8-sconst-p ()
  (if (sng8-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sng8-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sng8-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun sng8-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and its logical string recurrence.

(defun-sk sng8-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng8-is-sint8-p
       (sng8-to-sint8 value))
      (implies
       (sng8-is-sint8-p value)
       (equal
        (sng8-to-sint8 value)
        value))
      (equal
       (sng8-to-sint8
        (sng8-to-sint8 value))
       (sng8-to-sint8 value))))))

(defun-sk sng8-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng8-is-uint64-p
       (sng8-to-uint64 value))
      (implies
       (sng8-is-uint64-p value)
       (equal
        (sng8-to-uint64 value)
        value))
      (equal
       (sng8-to-uint64
        (sng8-to-uint64 value))
       (sng8-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sng8-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sng8-address-base address))
    (<= 0
        (sng8-address-offset address))
    (<=
     (+ (sng8-address-offset address)
        length)
     (sng8-allocation
      (sng8-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk sng8-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sng8-is-sint8-p
       (sng8-character-memory
        (sng8-shift address position)))))))

(defun-sk sng8-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sng8-character-memory
       (sng8-shift address index))
      0)
     (sng8-is-uint64-p index)
     (sng8-valid-rw-p
      (sng8-shift address 0)
      (+ 1 index))
     (sng8-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sng8-strlen-laws-p ()
  (forall (address)
    (implies
     (sng8-address-p address)
     (and
      (if
          (equal
           (sng8-character-memory
            (sng8-shift address 0))
           0)
          (equal
           (sng8-l-strlen address)
           0)
        (equal
         (sng8-to-uint64
          (+ 1
             (sng8-l-strlen
              (sng8-shift address 1))))
         (sng8-l-strlen address)))
      (sng8-is-uint64-p
       (sng8-l-strlen address))))))

;; Exact universal closure of A_Strchrnul.fix_l_strchrnul.

(defun-sk sng8-strchrnul-law-p ()
  (forall (address value)
    (implies
     (and
      (sng8-address-p address)
      (integerp value))
     (if
         (equal
          (sng8-character-memory address)
          value)
         (equal
          (sng8-l-strchrnul address value)
          address)
       (if
           (equal
            (sng8-character-memory address)
            0)
           (equal
            (sng8-l-strchrnul address value)
            address)
         (equal
          (sng8-l-strchrnul
           (sng8-shift address 1)
           value)
          (sng8-l-strchrnul address value)))))))

;; The final source hypothesis retains its universal quantifier over every
;; address rather than exposing a witness or restricting the carrier.

(defun-sk sng8-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (sng8-address-p candidate)
     (implies
      (sng8-addr-lt-p candidate current)
      (implies
       (sng8-addr-le-p start candidate)
       (not
        (equal
         (sng8-character-memory candidate)
         value)))))))

(defun-sk
    ntp4vc-strchrnul-assert-2-goal8-statement ()
  (forall
   (i a1 a)
   (implies
    (and
     (integerp i)
     (sng8-address-p a1)
     (sng8-address-p a)
     (sng8-function-types-p)
     (sng8-address-order-laws-p)
     (sng8-to-sint8-laws-p)
     (sng8-to-uint64-laws-p)
     (sng8-strlen-laws-p)
     (sng8-strchrnul-law-p))
    (let*
        ((x
          (sng8-to-sint8 i))
         (x1
          (sng8-l-strlen a1)))
      (implies
       (and
        (equal
         (sng8-character-memory a)
         0)
        (equal
         (sng8-l-strchrnul a1 x)
         (sng8-l-strchrnul a x))
        (<=
         (sng8-region
          (sng8-address-base a1))
         0)
        (sng8-linked-p)
        (sng8-sconst-p)
        (sng8-is-sint32-p i)
        (sng8-addr-le-p a1 a)
        (sng8-valid-string-p a)
        (sng8-valid-string-p a1)
        (sng8-addr-le-p
         a
         (sng8-shift a1 x1))
        (sng8-no-earlier-match-p
         a1 a x))
       (equal
        (+ (sng8-address-offset a1)
           x1)
        (sng8-address-offset a)))))))

(value-triple :itpeval-statement-checked)

:q
