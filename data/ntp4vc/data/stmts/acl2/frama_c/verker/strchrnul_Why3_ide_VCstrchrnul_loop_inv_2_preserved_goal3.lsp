;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchrnul_Why3_ide_VCstrchrnul_loop_inv_2_preserved_goal3:
;; preservation of the strchrnul loop's lower and upper address bounds after
;; advancing the current address by one, under the stated string-validity,
;; address-order, character, linkedness, constancy, and no-earlier-match
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun snlip2-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun snlip2-address-base (address)
  (car address))

(defun snlip2-address-offset (address)
  (cdr address))

(defun snlip2-shift (address amount)
  (cons
   (snlip2-address-base address)
   (+ (snlip2-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchrnul, C integer conversion,
;; linkedness, and constancy symbols.

(defstub snlip2-character-memory (address) t)
(defstub snlip2-allocation (index) t)
(defstub snlip2-region (base) t)
(defstub snlip2-addr-le-op (left right) t)
(defstub snlip2-addr-lt-op (left right) t)
(defstub snlip2-l-strlen (address) t)
(defstub snlip2-l-strchrnul (address value) t)
(defstub snlip2-to-uint8 (value) t)
(defstub snlip2-to-sint8 (value) t)
(defstub snlip2-to-uint64 (value) t)
(defstub snlip2-to-sint64 (value) t)
(defstub snlip2-linked-op () t)
(defstub snlip2-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk snlip2-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (snlip2-address-p address)
      (and
       (integerp
        (snlip2-character-memory address))
       (integerp
        (snlip2-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (snlip2-allocation index)))
     (implies
      (integerp base)
      (integerp
       (snlip2-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (snlip2-to-uint8 value))
       (integerp
        (snlip2-to-sint8 value))
       (integerp
        (snlip2-to-uint64 value))
       (integerp
        (snlip2-to-sint64 value))))
     (implies
      (and
       (snlip2-address-p address)
       (integerp value))
      (snlip2-address-p
       (snlip2-l-strchrnul address value))))))

(defun snlip2-addr-le-p (left right)
  (if (snlip2-addr-le-op left right) t nil))

(defun snlip2-addr-lt-p (left right)
  (if (snlip2-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; integer order on offsets.

(defun-sk snlip2-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (snlip2-address-p left)
      (snlip2-address-p right)
      (equal
       (snlip2-address-base left)
       (snlip2-address-base right)))
     (and
      (equal
       (snlip2-addr-le-p left right)
       (<=
        (snlip2-address-offset left)
        (snlip2-address-offset right)))
      (equal
       (snlip2-addr-lt-p left right)
       (<
        (snlip2-address-offset left)
        (snlip2-address-offset right)))))))

(defun snlip2-linked-p ()
  (if (snlip2-linked-op) t nil))

(defun snlip2-sconst-p ()
  (if (snlip2-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun snlip2-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun snlip2-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun snlip2-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun snlip2-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun snlip2-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and its logical string recurrences.

(defun-sk snlip2-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snlip2-is-uint8-p
       (snlip2-to-uint8 value))
      (implies
       (snlip2-is-uint8-p value)
       (equal
        (snlip2-to-uint8 value)
        value))
      (equal
       (snlip2-to-uint8
        (snlip2-to-uint8 value))
       (snlip2-to-uint8 value))))))

(defun-sk snlip2-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snlip2-is-sint8-p
       (snlip2-to-sint8 value))
      (implies
       (snlip2-is-sint8-p value)
       (equal
        (snlip2-to-sint8 value)
        value))
      (equal
       (snlip2-to-sint8
        (snlip2-to-sint8 value))
       (snlip2-to-sint8 value))))))

(defun-sk snlip2-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snlip2-is-uint64-p
       (snlip2-to-uint64 value))
      (implies
       (snlip2-is-uint64-p value)
       (equal
        (snlip2-to-uint64 value)
        value))
      (equal
       (snlip2-to-uint64
        (snlip2-to-uint64 value))
       (snlip2-to-uint64 value))))))

(defun-sk snlip2-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snlip2-is-sint64-p
       (snlip2-to-sint64 value))
      (implies
       (snlip2-is-sint64-p value)
       (equal
        (snlip2-to-sint64 value)
        value))
      (equal
       (snlip2-to-sint64
        (snlip2-to-sint64 value))
       (snlip2-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk snlip2-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (snlip2-to-sint8
        (snlip2-to-uint8 value))
       (snlip2-to-sint8 value))
      (equal
       (snlip2-to-sint64
        (snlip2-to-uint64 value))
       (snlip2-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun snlip2-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (snlip2-address-base address))
    (<= 0
        (snlip2-address-offset address))
    (<=
     (+ (snlip2-address-offset address)
        length)
     (snlip2-allocation
      (snlip2-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk snlip2-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (snlip2-is-sint8-p
       (snlip2-character-memory
        (snlip2-shift address position)))))))

(defun-sk snlip2-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snlip2-character-memory
       (snlip2-shift address index))
      0)
     (snlip2-is-uint64-p index)
     (snlip2-valid-rw-p
      (snlip2-shift address 0)
      (+ 1 index))
     (snlip2-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk snlip2-strlen-laws-p ()
  (forall (address)
    (implies
     (snlip2-address-p address)
     (and
      (if
          (equal
           (snlip2-character-memory
            (snlip2-shift address 0))
           0)
          (equal
           (snlip2-l-strlen address)
           0)
        (equal
         (snlip2-to-uint64
          (+ 1
             (snlip2-l-strlen
              (snlip2-shift address 1))))
         (snlip2-l-strlen address)))
      (snlip2-is-uint64-p
       (snlip2-l-strlen address))))))

;; Exact universal closure of A_Strchrnul.fix_l_strchrnul: both a matching
;; byte and the terminating null byte return the current address.

(defun-sk snlip2-strchrnul-law-p ()
  (forall (address value)
    (implies
     (and
      (snlip2-address-p address)
      (integerp value))
     (if
         (equal
          (snlip2-character-memory address)
          value)
         (equal
          (snlip2-l-strchrnul address value)
          address)
       (if
           (equal
            (snlip2-character-memory address)
            0)
           (equal
            (snlip2-l-strchrnul address value)
            address)
         (equal
          (snlip2-l-strchrnul
           (snlip2-shift address 1)
           value)
          (snlip2-l-strchrnul address value)))))))

;; The final source hypothesis retains its universal quantifier over every
;; address rather than exposing a witness or restricting the carrier.

(defun-sk snlip2-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (snlip2-address-p candidate)
     (implies
      (snlip2-addr-lt-p candidate current)
      (implies
       (snlip2-addr-le-p start candidate)
       (not
        (equal
         (snlip2-character-memory candidate)
         value)))))))

(defun-sk
    ntp4vc-strchrnul-loop-inv-2-preserved-goal3-statement ()
  (forall
   (a i a1)
   (implies
    (and
     (snlip2-address-p a)
     (integerp i)
     (snlip2-address-p a1)
     (snlip2-function-types-p)
     (snlip2-address-order-laws-p)
     (snlip2-to-uint8-laws-p)
     (snlip2-to-sint8-laws-p)
     (snlip2-to-uint64-laws-p)
     (snlip2-to-sint64-laws-p)
     (snlip2-signed-unsigned-projection-laws-p)
     (snlip2-strlen-laws-p)
     (snlip2-strchrnul-law-p))
    (let*
        ((x
          (snlip2-character-memory a))
         (x1
          (snlip2-to-sint8 i))
         (a2
          (snlip2-shift
           a1
           (snlip2-l-strlen a1)))
         (a3
          (snlip2-shift a 1)))
      (implies
       (and
        (not (equal x 0))
        (not (equal x x1))
        (equal
         (snlip2-l-strchrnul a1 x1)
         (snlip2-l-strchrnul a x1))
        (<=
         (snlip2-region
          (snlip2-address-base a1))
         0)
        (snlip2-linked-p)
        (snlip2-sconst-p)
        (snlip2-is-sint32-p i)
        (snlip2-addr-le-p a1 a)
        (snlip2-is-sint8-p x)
        (snlip2-valid-string-p a)
        (snlip2-valid-string-p a1)
        (snlip2-addr-le-p a a2)
        (snlip2-no-earlier-match-p
         a1 a x1))
       (and
        (snlip2-addr-le-p a1 a3)
        (snlip2-addr-le-p a3 a2)))))))

(value-triple :itpeval-statement-checked)

:q
