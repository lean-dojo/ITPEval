;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchrnul_Why3_ide_VCstrchrnul_not_exists_post_goal12:
;; the current address equals the logical end of the valid string when its
;; character is null or the searched signed byte, under the stated strchrnul,
;; address-order, linkedness, constancy, and no-prefix-match hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun snp12-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun snp12-address-base (address)
  (car address))

(defun snp12-address-offset (address)
  (cdr address))

(defun snp12-shift (address amount)
  (cons
   (snp12-address-base address)
   (+ (snp12-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchrnul, C integer conversion,
;; linkedness, and constancy symbols.

(defstub snp12-character-memory (address) t)
(defstub snp12-allocation (index) t)
(defstub snp12-region (base) t)
(defstub snp12-addr-le-op (left right) t)
(defstub snp12-addr-lt-op (left right) t)
(defstub snp12-l-strlen (address) t)
(defstub snp12-l-strchrnul (address value) t)
(defstub snp12-to-sint8 (value) t)
(defstub snp12-to-uint64 (value) t)
(defstub snp12-linked-op () t)
(defstub snp12-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk snp12-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (snp12-address-p address)
      (and
       (integerp
        (snp12-character-memory address))
       (integerp
        (snp12-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (snp12-allocation index)))
     (implies
      (integerp base)
      (integerp
       (snp12-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (snp12-to-sint8 value))
       (integerp
        (snp12-to-uint64 value))))
     (implies
      (and
       (snp12-address-p address)
       (integerp value))
      (snp12-address-p
       (snp12-l-strchrnul address value))))))

(defun snp12-addr-le-p (left right)
  (if (snp12-addr-le-op left right) t nil))

(defun snp12-addr-lt-p (left right)
  (if (snp12-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; integer order on offsets.

(defun-sk snp12-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (snp12-address-p left)
      (snp12-address-p right)
      (equal
       (snp12-address-base left)
       (snp12-address-base right)))
     (and
      (equal
       (snp12-addr-le-p left right)
       (<=
        (snp12-address-offset left)
        (snp12-address-offset right)))
      (equal
       (snp12-addr-lt-p left right)
       (<
        (snp12-address-offset left)
        (snp12-address-offset right)))))))

(defun snp12-linked-p ()
  (if (snp12-linked-op) t nil))

(defun snp12-sconst-p ()
  (if (snp12-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun snp12-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun snp12-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun snp12-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and its logical string recurrence.

(defun-sk snp12-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snp12-is-sint8-p
       (snp12-to-sint8 value))
      (implies
       (snp12-is-sint8-p value)
       (equal
        (snp12-to-sint8 value)
        value))
      (equal
       (snp12-to-sint8
        (snp12-to-sint8 value))
       (snp12-to-sint8 value))))))

(defun-sk snp12-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snp12-is-uint64-p
       (snp12-to-uint64 value))
      (implies
       (snp12-is-uint64-p value)
       (equal
        (snp12-to-uint64 value)
        value))
      (equal
       (snp12-to-uint64
        (snp12-to-uint64 value))
       (snp12-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun snp12-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (snp12-address-base address))
    (<= 0
        (snp12-address-offset address))
    (<=
     (+ (snp12-address-offset address)
        length)
     (snp12-allocation
      (snp12-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk snp12-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (snp12-is-sint8-p
       (snp12-character-memory
        (snp12-shift address position)))))))

(defun-sk snp12-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snp12-character-memory
       (snp12-shift address index))
      0)
     (snp12-is-uint64-p index)
     (snp12-valid-rw-p
      (snp12-shift address 0)
      (+ 1 index))
     (snp12-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk snp12-strlen-laws-p ()
  (forall (address)
    (implies
     (snp12-address-p address)
     (and
      (if
          (equal
           (snp12-character-memory
            (snp12-shift address 0))
           0)
          (equal
           (snp12-l-strlen address)
           0)
        (equal
         (snp12-to-uint64
          (+ 1
             (snp12-l-strlen
              (snp12-shift address 1))))
         (snp12-l-strlen address)))
      (snp12-is-uint64-p
       (snp12-l-strlen address))))))

;; Exact universal closure of A_Strchrnul.fix_l_strchrnul.

(defun-sk snp12-strchrnul-law-p ()
  (forall (address value)
    (implies
     (and
      (snp12-address-p address)
      (integerp value))
     (if
         (equal
          (snp12-character-memory address)
          value)
         (equal
          (snp12-l-strchrnul address value)
          address)
       (if
           (equal
            (snp12-character-memory address)
            0)
           (equal
            (snp12-l-strchrnul address value)
            address)
         (equal
          (snp12-l-strchrnul
           (snp12-shift address 1)
           value)
          (snp12-l-strchrnul address value)))))))

;; Preserve the source's two internal universal hypotheses over the full
;; address and mathematical-integer domains.

(defun-sk snp12-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (snp12-address-p candidate)
     (implies
      (snp12-addr-lt-p candidate current)
      (implies
       (snp12-addr-le-p start candidate)
       (not
        (equal
         (snp12-character-memory candidate)
         value)))))))

(defun-sk snp12-no-prefix-match-p
    (start bound value)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position bound)
       (not
        (equal
         (snp12-character-memory
          (snp12-shift start position))
         value)))))))

(defun-sk ntp4vc-strchrnul-not-exists-post-goal12-statement ()
  (forall
   (a a1 i)
   (implies
    (and
     (snp12-address-p a)
     (snp12-address-p a1)
     (integerp i)
     (snp12-function-types-p)
     (snp12-address-order-laws-p)
     (snp12-to-sint8-laws-p)
     (snp12-to-uint64-laws-p)
     (snp12-strlen-laws-p)
     (snp12-strchrnul-law-p))
    (let*
        ((x
          (snp12-to-sint8 i))
         (x1
          (snp12-character-memory a))
         (x2
          (snp12-l-strlen a1))
         (a2
          (snp12-shift a1 x2)))
      (implies
       (and
        (equal
         (snp12-l-strchrnul a1 x)
         (snp12-l-strchrnul a x))
        (<=
         (snp12-region
          (snp12-address-base a1))
         0)
        (snp12-linked-p)
        (snp12-sconst-p)
        (snp12-is-sint32-p i)
        (snp12-addr-le-p a1 a)
        (snp12-is-sint8-p x1)
        (snp12-valid-string-p a)
        (snp12-valid-string-p a1)
        (snp12-addr-le-p a a2)
        (implies
         (equal x1 0)
         (equal
          (+ (snp12-address-offset a1) x2)
          (snp12-address-offset a)))
        (or
         (equal x1 0)
         (equal x1 x))
        (snp12-no-earlier-match-p a1 a x)
        (snp12-no-prefix-match-p a1 x2 x))
       (equal a2 a))))))

(value-triple :itpeval-statement-checked)

:q
