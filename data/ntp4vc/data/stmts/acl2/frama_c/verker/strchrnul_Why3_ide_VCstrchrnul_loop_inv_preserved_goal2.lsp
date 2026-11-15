;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchrnul_Why3_ide_VCstrchrnul_loop_inv_preserved_goal2:
;; preservation of valid-string memory after the strchrnul loop advances the
;; current address by one, under the stated character, address-order,
;; linkedness, constancy, string-validity, and no-earlier-match hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun snlp2-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun snlp2-address-base (address)
  (car address))

(defun snlp2-address-offset (address)
  (cdr address))

(defun snlp2-shift (address amount)
  (cons
   (snlp2-address-base address)
   (+ (snlp2-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchrnul, C integer conversion,
;; linkedness, and constancy symbols.

(defstub snlp2-character-memory (address) t)
(defstub snlp2-allocation (index) t)
(defstub snlp2-region (base) t)
(defstub snlp2-addr-le-op (left right) t)
(defstub snlp2-addr-lt-op (left right) t)
(defstub snlp2-l-strlen (address) t)
(defstub snlp2-l-strchrnul (address value) t)
(defstub snlp2-to-uint8 (value) t)
(defstub snlp2-to-sint8 (value) t)
(defstub snlp2-to-uint64 (value) t)
(defstub snlp2-to-sint64 (value) t)
(defstub snlp2-linked-op () t)
(defstub snlp2-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk snlp2-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (snlp2-address-p address)
      (and
       (integerp
        (snlp2-character-memory address))
       (integerp
        (snlp2-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (snlp2-allocation index)))
     (implies
      (integerp base)
      (integerp
       (snlp2-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (snlp2-to-uint8 value))
       (integerp
        (snlp2-to-sint8 value))
       (integerp
        (snlp2-to-uint64 value))
       (integerp
        (snlp2-to-sint64 value))))
     (implies
      (and
       (snlp2-address-p address)
       (integerp value))
      (snlp2-address-p
       (snlp2-l-strchrnul address value))))))

(defun snlp2-addr-le-p (left right)
  (if (snlp2-addr-le-op left right) t nil))

(defun snlp2-addr-lt-p (left right)
  (if (snlp2-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; integer order on offsets.

(defun-sk snlp2-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (snlp2-address-p left)
      (snlp2-address-p right)
      (equal
       (snlp2-address-base left)
       (snlp2-address-base right)))
     (and
      (equal
       (snlp2-addr-le-p left right)
       (<=
        (snlp2-address-offset left)
        (snlp2-address-offset right)))
      (equal
       (snlp2-addr-lt-p left right)
       (<
        (snlp2-address-offset left)
        (snlp2-address-offset right)))))))

(defun snlp2-linked-p ()
  (if (snlp2-linked-op) t nil))

(defun snlp2-sconst-p ()
  (if (snlp2-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun snlp2-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun snlp2-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun snlp2-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun snlp2-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun snlp2-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and its logical string recurrence.

(defun-sk snlp2-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snlp2-is-uint8-p
       (snlp2-to-uint8 value))
      (implies
       (snlp2-is-uint8-p value)
       (equal
        (snlp2-to-uint8 value)
        value))
      (equal
       (snlp2-to-uint8
        (snlp2-to-uint8 value))
       (snlp2-to-uint8 value))))))

(defun-sk snlp2-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snlp2-is-sint8-p
       (snlp2-to-sint8 value))
      (implies
       (snlp2-is-sint8-p value)
       (equal
        (snlp2-to-sint8 value)
        value))
      (equal
       (snlp2-to-sint8
        (snlp2-to-sint8 value))
       (snlp2-to-sint8 value))))))

(defun-sk snlp2-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snlp2-is-uint64-p
       (snlp2-to-uint64 value))
      (implies
       (snlp2-is-uint64-p value)
       (equal
        (snlp2-to-uint64 value)
        value))
      (equal
       (snlp2-to-uint64
       (snlp2-to-uint64 value))
       (snlp2-to-uint64 value))))))

(defun-sk snlp2-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snlp2-is-sint64-p
       (snlp2-to-sint64 value))
      (implies
       (snlp2-is-sint64-p value)
       (equal
        (snlp2-to-sint64 value)
        value))
      (equal
       (snlp2-to-sint64
        (snlp2-to-sint64 value))
       (snlp2-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk snlp2-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (snlp2-to-sint8
        (snlp2-to-uint8 value))
       (snlp2-to-sint8 value))
      (equal
       (snlp2-to-sint64
        (snlp2-to-uint64 value))
       (snlp2-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun snlp2-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (snlp2-address-base address))
    (<= 0
        (snlp2-address-offset address))
    (<=
     (+ (snlp2-address-offset address)
        length)
     (snlp2-allocation
      (snlp2-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk snlp2-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (snlp2-is-sint8-p
       (snlp2-character-memory
        (snlp2-shift address position)))))))

(defun-sk snlp2-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snlp2-character-memory
       (snlp2-shift address index))
      0)
     (snlp2-is-uint64-p index)
     (snlp2-valid-rw-p
      (snlp2-shift address 0)
      (+ 1 index))
     (snlp2-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk snlp2-strlen-laws-p ()
  (forall (address)
    (implies
     (snlp2-address-p address)
     (and
      (if
          (equal
           (snlp2-character-memory
            (snlp2-shift address 0))
           0)
          (equal
           (snlp2-l-strlen address)
           0)
        (equal
         (snlp2-to-uint64
          (+ 1
             (snlp2-l-strlen
              (snlp2-shift address 1))))
         (snlp2-l-strlen address)))
      (snlp2-is-uint64-p
       (snlp2-l-strlen address))))))

;; Exact universal closure of A_Strchrnul.fix_l_strchrnul: both a matching
;; byte and the terminating null byte return the current address.

(defun-sk snlp2-strchrnul-law-p ()
  (forall (address value)
    (implies
     (and
      (snlp2-address-p address)
      (integerp value))
     (if
         (equal
          (snlp2-character-memory address)
          value)
         (equal
          (snlp2-l-strchrnul address value)
          address)
       (if
           (equal
            (snlp2-character-memory address)
            0)
           (equal
            (snlp2-l-strchrnul address value)
            address)
         (equal
          (snlp2-l-strchrnul
           (snlp2-shift address 1)
           value)
          (snlp2-l-strchrnul address value)))))))

;; The final source hypothesis retains its universal quantifier over every
;; address rather than exposing a witness or restricting the carrier.

(defun-sk snlp2-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (snlp2-address-p candidate)
     (implies
      (snlp2-addr-lt-p candidate current)
      (implies
       (snlp2-addr-le-p start candidate)
       (not
        (equal
         (snlp2-character-memory candidate)
         value)))))))

(defun-sk
    ntp4vc-strchrnul-loop-inv-preserved-goal2-statement ()
  (forall
   (a i a1)
   (implies
    (and
     (snlp2-address-p a)
     (integerp i)
     (snlp2-address-p a1)
     (snlp2-function-types-p)
     (snlp2-address-order-laws-p)
     (snlp2-to-uint8-laws-p)
     (snlp2-to-sint8-laws-p)
     (snlp2-to-uint64-laws-p)
     (snlp2-to-sint64-laws-p)
     (snlp2-signed-unsigned-projection-laws-p)
     (snlp2-strlen-laws-p)
     (snlp2-strchrnul-law-p))
    (let*
        ((x
          (snlp2-character-memory a))
         (x1
          (snlp2-to-sint8 i)))
      (implies
       (and
        (not (equal x 0))
        (not (equal x x1))
        (equal
         (snlp2-l-strchrnul a1 x1)
         (snlp2-l-strchrnul a x1))
        (<=
         (snlp2-region
          (snlp2-address-base a1))
         0)
        (snlp2-linked-p)
        (snlp2-sconst-p)
        (snlp2-is-sint32-p i)
        (snlp2-addr-le-p a1 a)
        (snlp2-is-sint8-p x)
        (snlp2-valid-string-p a)
        (snlp2-valid-string-p a1)
        (snlp2-addr-le-p
         a
         (snlp2-shift
          a1
          (snlp2-l-strlen a1)))
        (snlp2-no-earlier-match-p
         a1 a x1))
       (snlp2-valid-string-p
        (snlp2-shift a 1)))))))

(value-triple :itpeval-statement-checked)

:q
