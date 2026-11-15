;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchrnul_Why3_ide_VCstrchrnul_not_exists_post_2_goal13:
;; existence of an offset before the logical string length whose character
;; equals the current nonzero signed byte, under the stated strchrnul,
;; address-order, valid-string, linkedness, constancy, and no-earlier-match
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun snp2g13-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun snp2g13-address-base (address)
  (car address))

(defun snp2g13-address-offset (address)
  (cdr address))

(defun snp2g13-shift (address amount)
  (cons
   (snp2g13-address-base address)
   (+ (snp2g13-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchrnul, C integer conversion,
;; linkedness, and constancy symbols.

(defstub snp2g13-character-memory (address) t)
(defstub snp2g13-allocation (index) t)
(defstub snp2g13-region (base) t)
(defstub snp2g13-addr-le-op (left right) t)
(defstub snp2g13-addr-lt-op (left right) t)
(defstub snp2g13-l-strlen (address) t)
(defstub snp2g13-l-strchrnul (address value) t)
(defstub snp2g13-to-sint8 (value) t)
(defstub snp2g13-to-uint64 (value) t)
(defstub snp2g13-linked-op () t)
(defstub snp2g13-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk snp2g13-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (snp2g13-address-p address)
      (and
       (integerp
        (snp2g13-character-memory address))
       (integerp
        (snp2g13-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (snp2g13-allocation index)))
     (implies
      (integerp base)
      (integerp
       (snp2g13-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (snp2g13-to-sint8 value))
       (integerp
        (snp2g13-to-uint64 value))))
     (implies
      (and
       (snp2g13-address-p address)
       (integerp value))
      (snp2g13-address-p
       (snp2g13-l-strchrnul address value))))))

(defun snp2g13-addr-le-p (left right)
  (if (snp2g13-addr-le-op left right) t nil))

(defun snp2g13-addr-lt-p (left right)
  (if (snp2g13-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; integer order on offsets.

(defun-sk snp2g13-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (snp2g13-address-p left)
      (snp2g13-address-p right)
      (equal
       (snp2g13-address-base left)
       (snp2g13-address-base right)))
     (and
      (equal
       (snp2g13-addr-le-p left right)
       (<=
        (snp2g13-address-offset left)
        (snp2g13-address-offset right)))
      (equal
       (snp2g13-addr-lt-p left right)
       (<
        (snp2g13-address-offset left)
        (snp2g13-address-offset right)))))))

(defun snp2g13-linked-p ()
  (if (snp2g13-linked-op) t nil))

(defun snp2g13-sconst-p ()
  (if (snp2g13-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun snp2g13-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun snp2g13-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun snp2g13-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and its logical string recurrence.

(defun-sk snp2g13-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snp2g13-is-sint8-p
       (snp2g13-to-sint8 value))
      (implies
       (snp2g13-is-sint8-p value)
       (equal
        (snp2g13-to-sint8 value)
        value))
      (equal
       (snp2g13-to-sint8
        (snp2g13-to-sint8 value))
       (snp2g13-to-sint8 value))))))

(defun-sk snp2g13-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snp2g13-is-uint64-p
       (snp2g13-to-uint64 value))
      (implies
       (snp2g13-is-uint64-p value)
       (equal
        (snp2g13-to-uint64 value)
        value))
      (equal
       (snp2g13-to-uint64
        (snp2g13-to-uint64 value))
       (snp2g13-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun snp2g13-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (snp2g13-address-base address))
    (<= 0
        (snp2g13-address-offset address))
    (<=
     (+ (snp2g13-address-offset address)
        length)
     (snp2g13-allocation
      (snp2g13-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk snp2g13-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (snp2g13-is-sint8-p
       (snp2g13-character-memory
        (snp2g13-shift address position)))))))

(defun-sk snp2g13-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snp2g13-character-memory
       (snp2g13-shift address index))
      0)
     (snp2g13-is-uint64-p index)
     (snp2g13-valid-rw-p
      (snp2g13-shift address 0)
      (+ 1 index))
     (snp2g13-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk snp2g13-strlen-laws-p ()
  (forall (address)
    (implies
     (snp2g13-address-p address)
     (and
      (if
          (equal
           (snp2g13-character-memory
            (snp2g13-shift address 0))
           0)
          (equal
           (snp2g13-l-strlen address)
           0)
        (equal
         (snp2g13-to-uint64
          (+ 1
             (snp2g13-l-strlen
              (snp2g13-shift address 1))))
         (snp2g13-l-strlen address)))
      (snp2g13-is-uint64-p
       (snp2g13-l-strlen address))))))

;; Exact universal closure of A_Strchrnul.fix_l_strchrnul.

(defun-sk snp2g13-strchrnul-law-p ()
  (forall (address value)
    (implies
     (and
      (snp2g13-address-p address)
      (integerp value))
     (if
         (equal
          (snp2g13-character-memory address)
          value)
         (equal
          (snp2g13-l-strchrnul address value)
          address)
       (if
           (equal
            (snp2g13-character-memory address)
            0)
           (equal
            (snp2g13-l-strchrnul address value)
            address)
         (equal
          (snp2g13-l-strchrnul
           (snp2g13-shift address 1)
           value)
          (snp2g13-l-strchrnul address value)))))))

;; The penultimate source hypothesis retains its universal quantifier over
;; every address rather than restricting the carrier.

(defun-sk snp2g13-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (snp2g13-address-p candidate)
     (implies
      (snp2g13-addr-lt-p candidate current)
      (implies
       (snp2g13-addr-le-p start candidate)
       (not
        (equal
         value
         (snp2g13-character-memory candidate))))))))

;; The negated universal conclusion is represented directly, with the
;; quantified offset still internal and ranging over all mathematical
;; integers.

(defun-sk snp2g13-no-prefix-match-p
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
         (snp2g13-character-memory
          (snp2g13-shift start position))
         value)))))))

(defun-sk
    ntp4vc-strchrnul-not-exists-post-2-goal13-statement ()
  (forall
   (a a1 i)
   (implies
    (and
     (snp2g13-address-p a)
     (snp2g13-address-p a1)
     (integerp i)
     (snp2g13-function-types-p)
     (snp2g13-address-order-laws-p)
     (snp2g13-to-sint8-laws-p)
     (snp2g13-to-uint64-laws-p)
     (snp2g13-strlen-laws-p)
     (snp2g13-strchrnul-law-p))
    (let*
        ((x
          (snp2g13-character-memory a))
         (x1
          (snp2g13-l-strlen a1)))
      (implies
       (and
        (not (equal x 0))
        (equal
         x
         (snp2g13-to-sint8 i))
        (equal
         (snp2g13-l-strchrnul a1 x)
         (snp2g13-l-strchrnul a x))
        (<=
         (snp2g13-region
          (snp2g13-address-base a1))
         0)
        (snp2g13-linked-p)
        (snp2g13-sconst-p)
        (snp2g13-is-sint32-p i)
        (snp2g13-addr-le-p a1 a)
        (snp2g13-is-sint8-p x)
        (snp2g13-valid-string-p a)
        (snp2g13-valid-string-p a1)
        (snp2g13-addr-le-p
         a
         (snp2g13-shift a1 x1))
        (snp2g13-no-earlier-match-p
         a1 a x))
       (not
        (snp2g13-no-prefix-match-p
         a1 x1 x)))))))

(value-triple :itpeval-statement-checked)

:q
