;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchrnul_Why3_ide_VCstrchrnul_exists_post_goal10:
;; the character read at a strictly interior string offset is the null byte
;; when the current address has the logical endpoint offset and the two
;; logical strchrnul results agree, under the stated signed-byte,
;; address-order, valid-string, linkedness, constancy, and no-earlier-match
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sng10-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sng10-address-base (address)
  (car address))

(defun sng10-address-offset (address)
  (cdr address))

(defun sng10-shift (address amount)
  (cons
   (sng10-address-base address)
   (+ (sng10-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchrnul, C integer conversion,
;; linkedness, and constancy symbols.

(defstub sng10-character-memory (address) t)
(defstub sng10-allocation (index) t)
(defstub sng10-region (base) t)
(defstub sng10-addr-le-op (left right) t)
(defstub sng10-addr-lt-op (left right) t)
(defstub sng10-l-strlen (address) t)
(defstub sng10-l-strchrnul (address value) t)
(defstub sng10-to-sint8 (value) t)
(defstub sng10-to-uint64 (value) t)
(defstub sng10-linked-op () t)
(defstub sng10-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sng10-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (sng10-address-p address)
      (and
       (integerp
        (sng10-character-memory address))
       (integerp
        (sng10-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (sng10-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sng10-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (sng10-to-sint8 value))
       (integerp
        (sng10-to-uint64 value))))
     (implies
      (and
       (sng10-address-p address)
       (integerp value))
      (sng10-address-p
       (sng10-l-strchrnul address value))))))

(defun sng10-addr-le-p (left right)
  (if (sng10-addr-le-op left right) t nil))

(defun sng10-addr-lt-p (left right)
  (if (sng10-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; integer order on offsets.

(defun-sk sng10-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (sng10-address-p left)
      (sng10-address-p right)
      (equal
       (sng10-address-base left)
       (sng10-address-base right)))
     (and
      (equal
       (sng10-addr-le-p left right)
       (<=
        (sng10-address-offset left)
        (sng10-address-offset right)))
      (equal
       (sng10-addr-lt-p left right)
       (<
        (sng10-address-offset left)
        (sng10-address-offset right)))))))

(defun sng10-linked-p ()
  (if (sng10-linked-op) t nil))

(defun sng10-sconst-p ()
  (if (sng10-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sng10-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sng10-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun sng10-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and its logical string recurrence.

(defun-sk sng10-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng10-is-sint8-p
       (sng10-to-sint8 value))
      (implies
       (sng10-is-sint8-p value)
       (equal
        (sng10-to-sint8 value)
        value))
      (equal
       (sng10-to-sint8
        (sng10-to-sint8 value))
       (sng10-to-sint8 value))))))

(defun-sk sng10-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sng10-is-uint64-p
       (sng10-to-uint64 value))
      (implies
       (sng10-is-uint64-p value)
       (equal
        (sng10-to-uint64 value)
        value))
      (equal
       (sng10-to-uint64
        (sng10-to-uint64 value))
       (sng10-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sng10-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sng10-address-base address))
    (<= 0
        (sng10-address-offset address))
    (<=
     (+ (sng10-address-offset address)
        length)
     (sng10-allocation
      (sng10-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk sng10-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sng10-is-sint8-p
       (sng10-character-memory
        (sng10-shift address position)))))))

(defun-sk sng10-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sng10-character-memory
       (sng10-shift address index))
      0)
     (sng10-is-uint64-p index)
     (sng10-valid-rw-p
      (sng10-shift address 0)
      (+ 1 index))
     (sng10-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sng10-strlen-laws-p ()
  (forall (address)
    (implies
     (sng10-address-p address)
     (and
      (if
          (equal
           (sng10-character-memory
            (sng10-shift address 0))
           0)
          (equal
           (sng10-l-strlen address)
           0)
        (equal
         (sng10-to-uint64
          (+ 1
             (sng10-l-strlen
              (sng10-shift address 1))))
         (sng10-l-strlen address)))
      (sng10-is-uint64-p
       (sng10-l-strlen address))))))

;; Exact universal closure of A_Strchrnul.fix_l_strchrnul.

(defun-sk sng10-strchrnul-law-p ()
  (forall (address value)
    (implies
     (and
      (sng10-address-p address)
      (integerp value))
     (if
         (equal
          (sng10-character-memory address)
          value)
         (equal
          (sng10-l-strchrnul address value)
          address)
       (if
           (equal
            (sng10-character-memory address)
            0)
           (equal
            (sng10-l-strchrnul address value)
            address)
         (equal
          (sng10-l-strchrnul
           (sng10-shift address 1)
           value)
          (sng10-l-strchrnul address value)))))))

;; The final source hypothesis retains its universal quantifier over every
;; address rather than exposing a witness or restricting the carrier.

(defun-sk sng10-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (sng10-address-p candidate)
     (implies
      (sng10-addr-lt-p candidate current)
      (implies
       (sng10-addr-le-p start candidate)
       (not
        (equal
         (sng10-character-memory candidate)
         value)))))))

(defun-sk
    ntp4vc-strchrnul-exists-post-goal10-statement ()
  (forall
   (a1 i a i1)
   (implies
    (and
     (sng10-address-p a1)
     (integerp i)
     (sng10-address-p a)
     (integerp i1)
     (sng10-function-types-p)
     (sng10-address-order-laws-p)
     (sng10-to-sint8-laws-p)
     (sng10-to-uint64-laws-p)
     (sng10-strlen-laws-p)
     (sng10-strchrnul-law-p))
    (let*
        ((x
          (sng10-character-memory
           (sng10-shift a1 i)))
         (x1
          (sng10-l-strlen a1)))
      (implies
       (and
        (equal
         (sng10-character-memory a)
         0)
        (equal
         x
         (sng10-to-sint8 i1))
        (equal
         (+ (sng10-address-offset a1)
            x1)
         (sng10-address-offset a))
        (equal
         (sng10-l-strchrnul a1 x)
         (sng10-l-strchrnul a x))
        (<= 0 i)
        (< i x1)
        (<=
         (sng10-region
          (sng10-address-base a1))
         0)
        (sng10-linked-p)
        (sng10-sconst-p)
        (sng10-is-sint32-p i1)
        (sng10-addr-le-p a1 a)
        (sng10-valid-string-p a)
        (sng10-valid-string-p a1)
        (sng10-addr-le-p
         a
         (sng10-shift a1 x1))
        (sng10-no-earlier-match-p
         a1 a x))
       (equal x 0))))))

(value-triple :itpeval-statement-checked)

:q
