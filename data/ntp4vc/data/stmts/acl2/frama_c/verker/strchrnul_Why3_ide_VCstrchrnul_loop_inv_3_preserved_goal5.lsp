;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchrnul_Why3_ide_VCstrchrnul_loop_inv_3_preserved_goal5:
;; preservation of the strchrnul loop invariant stating that the character at
;; the constrained current address differs from the searched signed byte.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sng5-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sng5-address-base (address)
  (car address))

(defun sng5-address-offset (address)
  (cdr address))

(defun sng5-shift (address amount)
  (cons
   (sng5-address-base address)
   (+ (sng5-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchrnul, C integer conversions,
;; linkedness, and constancy symbols.

(defstub sng5-character-memory (address) t)
(defstub sng5-allocation (index) t)
(defstub sng5-region (base) t)
(defstub sng5-addr-le-op (left right) t)
(defstub sng5-addr-lt-op (left right) t)
(defstub sng5-l-strlen (address) t)
(defstub sng5-l-strchrnul (address value) t)
(defstub sng5-to-uint8 (value) t)
(defstub sng5-to-sint8 (value) t)
(defstub sng5-to-uint64 (value) t)
(defstub sng5-to-sint64 (value) t)
(defstub sng5-linked-op () t)
(defstub sng5-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sng5-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (sng5-address-p address)
      (and
       (integerp
        (sng5-character-memory address))
       (integerp
        (sng5-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (sng5-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sng5-region base)))
     (implies
     (integerp value)
      (and
       (integerp
        (sng5-to-uint8 value))
       (integerp
        (sng5-to-sint8 value))
       (integerp
        (sng5-to-uint64 value))
       (integerp
        (sng5-to-sint64 value))))
     (implies
      (and
       (sng5-address-p address)
       (integerp value))
      (sng5-address-p
       (sng5-l-strchrnul address value))))))

(defun sng5-addr-le-p (left right)
  (if (sng5-addr-le-op left right) t nil))

(defun sng5-addr-lt-p (left right)
  (if (sng5-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; integer order on offsets.

(defun-sk sng5-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (sng5-address-p left)
      (sng5-address-p right)
      (equal
       (sng5-address-base left)
       (sng5-address-base right)))
     (and
      (equal
       (sng5-addr-le-p left right)
       (<=
        (sng5-address-offset left)
        (sng5-address-offset right)))
      (equal
       (sng5-addr-lt-p left right)
       (<
        (sng5-address-offset left)
        (sng5-address-offset right)))))))

(defun sng5-linked-p ()
  (if (sng5-linked-op) t nil))

(defun sng5-sconst-p ()
  (if (sng5-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sng5-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sng5-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun sng5-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun sng5-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun sng5-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and its logical string recurrence.

(defun-sk sng5-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng5-is-uint8-p
       (sng5-to-uint8 value))
      (implies
       (sng5-is-uint8-p value)
       (equal
        (sng5-to-uint8 value)
        value))
      (equal
       (sng5-to-uint8
        (sng5-to-uint8 value))
       (sng5-to-uint8 value))))))

(defun-sk sng5-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng5-is-sint8-p
       (sng5-to-sint8 value))
      (implies
       (sng5-is-sint8-p value)
       (equal
        (sng5-to-sint8 value)
        value))
      (equal
       (sng5-to-sint8
        (sng5-to-sint8 value))
       (sng5-to-sint8 value))))))

(defun-sk sng5-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng5-is-uint64-p
       (sng5-to-uint64 value))
      (implies
       (sng5-is-uint64-p value)
       (equal
        (sng5-to-uint64 value)
        value))
      (equal
       (sng5-to-uint64
       (sng5-to-uint64 value))
       (sng5-to-uint64 value))))))

(defun-sk sng5-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng5-is-sint64-p
       (sng5-to-sint64 value))
      (implies
       (sng5-is-sint64-p value)
       (equal
        (sng5-to-sint64 value)
        value))
      (equal
       (sng5-to-sint64
        (sng5-to-sint64 value))
       (sng5-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk sng5-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (sng5-to-sint8
        (sng5-to-uint8 value))
       (sng5-to-sint8 value))
      (equal
       (sng5-to-sint64
        (sng5-to-uint64 value))
       (sng5-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sng5-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sng5-address-base address))
    (<= 0
        (sng5-address-offset address))
    (<=
     (+ (sng5-address-offset address)
        length)
     (sng5-allocation
      (sng5-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk sng5-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sng5-is-sint8-p
       (sng5-character-memory
        (sng5-shift address position)))))))

(defun-sk sng5-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sng5-character-memory
       (sng5-shift address index))
      0)
     (sng5-is-uint64-p index)
     (sng5-valid-rw-p
      (sng5-shift address 0)
      (+ 1 index))
     (sng5-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sng5-strlen-laws-p ()
  (forall (address)
    (implies
     (sng5-address-p address)
     (and
      (if
          (equal
           (sng5-character-memory
            (sng5-shift address 0))
           0)
          (equal
           (sng5-l-strlen address)
           0)
        (equal
         (sng5-to-uint64
          (+ 1
             (sng5-l-strlen
              (sng5-shift address 1))))
         (sng5-l-strlen address)))
      (sng5-is-uint64-p
       (sng5-l-strlen address))))))

;; Exact universal closure of A_Strchrnul.fix_l_strchrnul: both a matching
;; byte and the terminating null byte return the current address.

(defun-sk sng5-strchrnul-law-p ()
  (forall (address value)
    (implies
     (and
      (sng5-address-p address)
      (integerp value))
     (if
         (equal
          (sng5-character-memory address)
          value)
         (equal
          (sng5-l-strchrnul address value)
          address)
       (if
           (equal
            (sng5-character-memory address)
            0)
           (equal
            (sng5-l-strchrnul address value)
            address)
         (equal
          (sng5-l-strchrnul
           (sng5-shift address 1)
           value)
          (sng5-l-strchrnul address value)))))))

;; The source loop-invariant hypothesis retains its universal quantifier over
;; every address rather than restricting the address carrier.

(defun-sk sng5-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (sng5-address-p candidate)
     (implies
      (sng5-addr-lt-p candidate current)
      (implies
       (sng5-addr-le-p start candidate)
       (not
        (equal
         (sng5-character-memory candidate)
         value)))))))

(defun-sk
    ntp4vc-strchrnul-loop-inv-3-preserved-goal5-statement ()
  (forall
   (a i a1 a2)
   (implies
    (and
     (sng5-address-p a)
     (integerp i)
     (sng5-address-p a1)
     (sng5-address-p a2)
     (sng5-function-types-p)
     (sng5-address-order-laws-p)
     (sng5-to-uint8-laws-p)
     (sng5-to-sint8-laws-p)
     (sng5-to-uint64-laws-p)
     (sng5-to-sint64-laws-p)
     (sng5-signed-unsigned-projection-laws-p)
     (sng5-strlen-laws-p)
     (sng5-strchrnul-law-p))
    (let*
        ((x
          (sng5-character-memory a))
         (x1
          (sng5-to-sint8 i)))
      (implies
       (and
        (not (equal x 0))
        (not (equal x x1))
        (equal
         (sng5-l-strchrnul a1 x1)
         (sng5-l-strchrnul a x1))
        (<=
         (sng5-region
          (sng5-address-base a1))
         0)
        (sng5-linked-p)
        (sng5-sconst-p)
        (sng5-is-sint32-p i)
        (sng5-addr-le-p a1 a)
        (sng5-addr-le-p a1 a2)
        (sng5-is-sint8-p x)
        (sng5-valid-string-p a)
        (sng5-valid-string-p a1)
        (sng5-addr-lt-p
         a2
         (sng5-shift a 1))
        (sng5-addr-le-p
         a
         (sng5-shift
          a1
          (sng5-l-strlen a1)))
        (sng5-no-earlier-match-p
         a1 a x1))
       (not
        (equal
         (sng5-character-memory a2)
         x1)))))))

(value-triple :itpeval-statement-checked)

:q
