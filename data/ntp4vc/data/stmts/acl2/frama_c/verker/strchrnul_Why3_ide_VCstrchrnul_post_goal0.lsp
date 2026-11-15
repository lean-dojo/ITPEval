;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchrnul_Why3_ide_VCstrchrnul_post_goal0:
;; the starting and current addresses have the same base when their logical
;; strchrnul results agree, under the stated address-order, valid-string,
;; signed-byte, linkedness, constancy, endpoint, and no-earlier-match
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun spg0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun spg0-address-base (address)
  (car address))

(defun spg0-address-offset (address)
  (cdr address))

(defun spg0-shift (address amount)
  (cons
   (spg0-address-base address)
   (+ (spg0-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchrnul, C integer conversions,
;; linkedness, and constancy symbols.

(defstub spg0-character-memory (address) t)
(defstub spg0-allocation (index) t)
(defstub spg0-region (base) t)
(defstub spg0-addr-le-op (left right) t)
(defstub spg0-addr-lt-op (left right) t)
(defstub spg0-l-strlen (address) t)
(defstub spg0-l-strchrnul (address value) t)
(defstub spg0-to-uint8 (value) t)
(defstub spg0-to-sint8 (value) t)
(defstub spg0-to-uint64 (value) t)
(defstub spg0-to-sint64 (value) t)
(defstub spg0-linked-op () t)
(defstub spg0-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk spg0-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (spg0-address-p address)
      (and
       (integerp
        (spg0-character-memory address))
       (integerp
        (spg0-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (spg0-allocation index)))
     (implies
      (integerp base)
      (integerp
       (spg0-region base)))
     (implies
     (integerp value)
      (and
       (integerp
        (spg0-to-uint8 value))
       (integerp
        (spg0-to-sint8 value))
       (integerp
        (spg0-to-uint64 value))
       (integerp
        (spg0-to-sint64 value))))
     (implies
      (and
       (spg0-address-p address)
       (integerp value))
      (spg0-address-p
       (spg0-l-strchrnul address value))))))

(defun spg0-addr-le-p (left right)
  (if (spg0-addr-le-op left right) t nil))

(defun spg0-addr-lt-p (left right)
  (if (spg0-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; integer order on offsets.

(defun-sk spg0-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (spg0-address-p left)
      (spg0-address-p right)
      (equal
       (spg0-address-base left)
       (spg0-address-base right)))
     (and
      (equal
       (spg0-addr-le-p left right)
       (<=
        (spg0-address-offset left)
        (spg0-address-offset right)))
      (equal
       (spg0-addr-lt-p left right)
       (<
        (spg0-address-offset left)
        (spg0-address-offset right)))))))

(defun spg0-linked-p ()
  (if (spg0-linked-op) t nil))

(defun spg0-sconst-p ()
  (if (spg0-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun spg0-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun spg0-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun spg0-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun spg0-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun spg0-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and its logical string recurrence.

(defun-sk spg0-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spg0-is-uint8-p
       (spg0-to-uint8 value))
      (implies
       (spg0-is-uint8-p value)
       (equal
        (spg0-to-uint8 value)
        value))
      (equal
       (spg0-to-uint8
        (spg0-to-uint8 value))
       (spg0-to-uint8 value))))))

(defun-sk spg0-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spg0-is-sint8-p
       (spg0-to-sint8 value))
      (implies
       (spg0-is-sint8-p value)
       (equal
        (spg0-to-sint8 value)
        value))
      (equal
       (spg0-to-sint8
        (spg0-to-sint8 value))
       (spg0-to-sint8 value))))))

(defun-sk spg0-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spg0-is-uint64-p
       (spg0-to-uint64 value))
      (implies
       (spg0-is-uint64-p value)
       (equal
        (spg0-to-uint64 value)
        value))
      (equal
       (spg0-to-uint64
       (spg0-to-uint64 value))
       (spg0-to-uint64 value))))))

(defun-sk spg0-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (spg0-is-sint64-p
       (spg0-to-sint64 value))
      (implies
       (spg0-is-sint64-p value)
       (equal
        (spg0-to-sint64 value)
        value))
      (equal
       (spg0-to-sint64
        (spg0-to-sint64 value))
       (spg0-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk spg0-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (spg0-to-sint8
        (spg0-to-uint8 value))
       (spg0-to-sint8 value))
      (equal
       (spg0-to-sint64
        (spg0-to-uint64 value))
       (spg0-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun spg0-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (spg0-address-base address))
    (<= 0
        (spg0-address-offset address))
    (<=
     (+ (spg0-address-offset address)
        length)
     (spg0-allocation
      (spg0-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk spg0-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (spg0-is-sint8-p
       (spg0-character-memory
        (spg0-shift address position)))))))

(defun-sk spg0-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (spg0-character-memory
       (spg0-shift address index))
      0)
     (spg0-is-uint64-p index)
     (spg0-valid-rw-p
      (spg0-shift address 0)
      (+ 1 index))
     (spg0-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk spg0-strlen-laws-p ()
  (forall (address)
    (implies
     (spg0-address-p address)
     (and
      (if
          (equal
           (spg0-character-memory
            (spg0-shift address 0))
           0)
          (equal
           (spg0-l-strlen address)
           0)
        (equal
         (spg0-to-uint64
          (+ 1
             (spg0-l-strlen
              (spg0-shift address 1))))
         (spg0-l-strlen address)))
      (spg0-is-uint64-p
       (spg0-l-strlen address))))))

;; Exact universal closure of A_Strchrnul.fix_l_strchrnul.

(defun-sk spg0-strchrnul-law-p ()
  (forall (address value)
    (implies
     (and
      (spg0-address-p address)
      (integerp value))
     (if
         (equal
          (spg0-character-memory address)
          value)
         (equal
          (spg0-l-strchrnul address value)
          address)
       (if
           (equal
            (spg0-character-memory address)
            0)
           (equal
            (spg0-l-strchrnul address value)
            address)
         (equal
          (spg0-l-strchrnul
           (spg0-shift address 1)
           value)
          (spg0-l-strchrnul address value)))))))

;; The final source hypothesis retains its universal quantifier over every
;; address rather than exposing a witness or restricting the carrier.

(defun-sk spg0-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (spg0-address-p candidate)
     (implies
      (spg0-addr-lt-p candidate current)
      (implies
       (spg0-addr-le-p start candidate)
       (not
        (equal
         (spg0-character-memory candidate)
         value)))))))

(defun-sk ntp4vc-strchrnul-post-goal0-statement ()
  (forall
   (i a1 a)
   (implies
    (and
     (integerp i)
     (spg0-address-p a1)
     (spg0-address-p a)
     (spg0-function-types-p)
     (spg0-address-order-laws-p)
     (spg0-to-uint8-laws-p)
     (spg0-to-sint8-laws-p)
     (spg0-to-uint64-laws-p)
     (spg0-to-sint64-laws-p)
     (spg0-signed-unsigned-projection-laws-p)
     (spg0-strlen-laws-p)
     (spg0-strchrnul-law-p))
    (let*
        ((x
          (spg0-to-sint8 i))
         (x1
          (spg0-address-base a1))
         (x2
          (spg0-character-memory a))
         (x3
          (spg0-l-strlen a1)))
      (implies
       (and
        (equal
         (spg0-l-strchrnul a1 x)
         (spg0-l-strchrnul a x))
        (<=
         (spg0-region x1)
         0)
        (spg0-linked-p)
        (spg0-sconst-p)
        (spg0-is-sint32-p i)
        (spg0-addr-le-p a1 a)
        (spg0-is-sint8-p x2)
        (spg0-valid-string-p a)
        (spg0-valid-string-p a1)
        (spg0-addr-le-p
         a
         (spg0-shift a1 x3))
        (implies
         (equal x2 0)
         (equal
          (+ (spg0-address-offset a1) x3)
          (spg0-address-offset a)))
        (or
         (equal x2 0)
         (equal x2 x))
        (spg0-no-earlier-match-p a1 a x))
       (equal
        x1
        (spg0-address-base a)))))))

(value-triple :itpeval-statement-checked)

:q
