;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchrnul_Why3_ide_VCstrchrnul_loop_term_positive_goal9:
;; the current address offset does not exceed the valid string's logical
;; endpoint, under the stated character, strchrnul-result, address-order,
;; linkedness, constancy, string-validity, and no-earlier-match hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sntg9-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sntg9-address-base (address)
  (car address))

(defun sntg9-address-offset (address)
  (cdr address))

(defun sntg9-shift (address amount)
  (cons
   (sntg9-address-base address)
   (+ (sntg9-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchrnul, C integer conversion,
;; linkedness, and constancy symbols.

(defstub sntg9-character-memory (address) t)
(defstub sntg9-allocation (index) t)
(defstub sntg9-region (base) t)
(defstub sntg9-addr-le-op (left right) t)
(defstub sntg9-addr-lt-op (left right) t)
(defstub sntg9-l-strlen (address) t)
(defstub sntg9-l-strchrnul (address value) t)
(defstub sntg9-to-uint8 (value) t)
(defstub sntg9-to-sint8 (value) t)
(defstub sntg9-to-uint64 (value) t)
(defstub sntg9-to-sint64 (value) t)
(defstub sntg9-linked-op () t)
(defstub sntg9-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sntg9-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (sntg9-address-p address)
      (and
       (integerp
        (sntg9-character-memory address))
       (integerp
        (sntg9-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (sntg9-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sntg9-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (sntg9-to-uint8 value))
       (integerp
        (sntg9-to-sint8 value))
       (integerp
        (sntg9-to-uint64 value))
       (integerp
        (sntg9-to-sint64 value))))
     (implies
      (and
       (sntg9-address-p address)
       (integerp value))
      (sntg9-address-p
       (sntg9-l-strchrnul address value))))))

(defun sntg9-addr-le-p (left right)
  (if (sntg9-addr-le-op left right) t nil))

(defun sntg9-addr-lt-p (left right)
  (if (sntg9-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; integer order on offsets.

(defun-sk sntg9-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (sntg9-address-p left)
      (sntg9-address-p right)
      (equal
       (sntg9-address-base left)
       (sntg9-address-base right)))
     (and
      (equal
       (sntg9-addr-le-p left right)
       (<=
        (sntg9-address-offset left)
        (sntg9-address-offset right)))
      (equal
       (sntg9-addr-lt-p left right)
       (<
        (sntg9-address-offset left)
        (sntg9-address-offset right)))))))

(defun sntg9-linked-p ()
  (if (sntg9-linked-op) t nil))

(defun sntg9-sconst-p ()
  (if (sntg9-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sntg9-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sntg9-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun sntg9-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun sntg9-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun sntg9-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and its logical string recurrence.

(defun-sk sntg9-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sntg9-is-uint8-p
       (sntg9-to-uint8 value))
      (implies
       (sntg9-is-uint8-p value)
       (equal
        (sntg9-to-uint8 value)
        value))
      (equal
       (sntg9-to-uint8
        (sntg9-to-uint8 value))
       (sntg9-to-uint8 value))))))

(defun-sk sntg9-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sntg9-is-sint8-p
       (sntg9-to-sint8 value))
      (implies
       (sntg9-is-sint8-p value)
       (equal
        (sntg9-to-sint8 value)
        value))
      (equal
       (sntg9-to-sint8
        (sntg9-to-sint8 value))
       (sntg9-to-sint8 value))))))

(defun-sk sntg9-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sntg9-is-uint64-p
       (sntg9-to-uint64 value))
      (implies
       (sntg9-is-uint64-p value)
       (equal
        (sntg9-to-uint64 value)
        value))
      (equal
       (sntg9-to-uint64
        (sntg9-to-uint64 value))
       (sntg9-to-uint64 value))))))

(defun-sk sntg9-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sntg9-is-sint64-p
       (sntg9-to-sint64 value))
      (implies
       (sntg9-is-sint64-p value)
       (equal
        (sntg9-to-sint64 value)
        value))
      (equal
       (sntg9-to-sint64
        (sntg9-to-sint64 value))
       (sntg9-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk sntg9-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (sntg9-to-sint8
        (sntg9-to-uint8 value))
       (sntg9-to-sint8 value))
      (equal
       (sntg9-to-sint64
        (sntg9-to-uint64 value))
       (sntg9-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sntg9-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sntg9-address-base address))
    (<= 0
        (sntg9-address-offset address))
    (<=
     (+ (sntg9-address-offset address)
        length)
     (sntg9-allocation
      (sntg9-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk sntg9-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sntg9-is-sint8-p
       (sntg9-character-memory
        (sntg9-shift address position)))))))

(defun-sk sntg9-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sntg9-character-memory
       (sntg9-shift address index))
      0)
     (sntg9-is-uint64-p index)
     (sntg9-valid-rw-p
      (sntg9-shift address 0)
      (+ 1 index))
     (sntg9-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sntg9-strlen-laws-p ()
  (forall (address)
    (implies
     (sntg9-address-p address)
     (and
      (if
          (equal
           (sntg9-character-memory
            (sntg9-shift address 0))
           0)
          (equal
           (sntg9-l-strlen address)
           0)
        (equal
         (sntg9-to-uint64
          (+ 1
             (sntg9-l-strlen
              (sntg9-shift address 1))))
         (sntg9-l-strlen address)))
      (sntg9-is-uint64-p
       (sntg9-l-strlen address))))))

;; Exact universal closure of A_Strchrnul.fix_l_strchrnul.

(defun-sk sntg9-strchrnul-law-p ()
  (forall (address value)
    (implies
     (and
      (sntg9-address-p address)
      (integerp value))
     (if
         (equal
          (sntg9-character-memory address)
          value)
         (equal
          (sntg9-l-strchrnul address value)
          address)
       (if
           (equal
            (sntg9-character-memory address)
            0)
           (equal
            (sntg9-l-strchrnul address value)
            address)
         (equal
          (sntg9-l-strchrnul
           (sntg9-shift address 1)
           value)
          (sntg9-l-strchrnul address value)))))))

;; The final source hypothesis retains its universal quantifier over every
;; address rather than exposing a witness or restricting the carrier.

(defun-sk sntg9-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (sntg9-address-p candidate)
     (implies
      (sntg9-addr-lt-p candidate current)
      (implies
       (sntg9-addr-le-p start candidate)
       (not
        (equal
         (sntg9-character-memory candidate)
         value)))))))

(defun-sk
    ntp4vc-strchrnul-loop-term-positive-goal9-statement ()
  (forall
   (a i a1)
   (implies
    (and
     (sntg9-address-p a)
     (integerp i)
     (sntg9-address-p a1)
     (sntg9-function-types-p)
     (sntg9-address-order-laws-p)
     (sntg9-to-uint8-laws-p)
     (sntg9-to-sint8-laws-p)
     (sntg9-to-uint64-laws-p)
     (sntg9-to-sint64-laws-p)
     (sntg9-signed-unsigned-projection-laws-p)
     (sntg9-strlen-laws-p)
     (sntg9-strchrnul-law-p))
    (let*
        ((x
          (sntg9-character-memory a))
         (x1
          (sntg9-to-sint8 i))
         (x2
          (sntg9-l-strlen a1)))
      (implies
       (and
        (not (equal x 0))
        (not (equal x x1))
        (equal
         (sntg9-l-strchrnul a1 x1)
         (sntg9-l-strchrnul a x1))
        (<=
         (sntg9-region
          (sntg9-address-base a1))
         0)
        (sntg9-linked-p)
        (sntg9-sconst-p)
        (sntg9-is-sint32-p i)
        (sntg9-addr-le-p a1 a)
        (sntg9-is-sint8-p x)
        (sntg9-valid-string-p a)
        (sntg9-valid-string-p a1)
        (sntg9-addr-le-p
         a
         (sntg9-shift
          a1
          x2))
        (sntg9-no-earlier-match-p
         a1 a x1))
       (<=
        (sntg9-address-offset a)
        (+
         (sntg9-address-offset a1)
         x2)))))))

(value-triple :itpeval-statement-checked)

:q
