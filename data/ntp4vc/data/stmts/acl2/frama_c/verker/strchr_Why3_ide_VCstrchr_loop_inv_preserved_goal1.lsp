;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchr_Why3_ide_VCstrchr_loop_inv_preserved_goal1:
;; preservation of valid-string memory after the strchr loop advances the
;; current address by one, under the stated character, address-order,
;; linkedness, constancy, string-validity, and no-earlier-match hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sclp1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sclp1-address-base (address)
  (car address))

(defun sclp1-address-offset (address)
  (cdr address))

(defun sclp1-shift (address amount)
  (cons
   (sclp1-address-base address)
   (+ (sclp1-address-offset address) amount)))

(defun sclp1-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchr, C integer conversion,
;; linkedness, and constancy symbols.

(defstub sclp1-character-memory (address) t)
(defstub sclp1-allocation (index) t)
(defstub sclp1-region (base) t)
(defstub sclp1-addr-le-op (left right) t)
(defstub sclp1-addr-lt-op (left right) t)
(defstub sclp1-l-strlen (address) t)
(defstub sclp1-l-strchr (address value) t)
(defstub sclp1-to-sint8 (value) t)
(defstub sclp1-to-uint64 (value) t)
(defstub sclp1-linked-op () t)
(defstub sclp1-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sclp1-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (sclp1-address-p address)
      (and
       (integerp
        (sclp1-character-memory address))
       (integerp
        (sclp1-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (sclp1-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sclp1-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (sclp1-to-sint8 value))
       (integerp
        (sclp1-to-uint64 value))))
     (implies
      (and
       (sclp1-address-p address)
       (integerp value))
      (sclp1-address-p
       (sclp1-l-strchr address value))))))

(defun sclp1-addr-le-p (left right)
  (if (sclp1-addr-le-op left right) t nil))

(defun sclp1-addr-lt-p (left right)
  (if (sclp1-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; integer order on offsets.

(defun-sk sclp1-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (sclp1-address-p left)
      (sclp1-address-p right)
      (equal
       (sclp1-address-base left)
       (sclp1-address-base right)))
     (and
      (equal
       (sclp1-addr-le-p left right)
       (<=
        (sclp1-address-offset left)
        (sclp1-address-offset right)))
      (equal
       (sclp1-addr-lt-p left right)
       (<
        (sclp1-address-offset left)
        (sclp1-address-offset right)))))))

(defun sclp1-linked-p ()
  (if (sclp1-linked-op) t nil))

(defun sclp1-sconst-p ()
  (if (sclp1-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sclp1-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sclp1-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun sclp1-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and its logical string recurrence.

(defun-sk sclp1-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sclp1-is-sint8-p
       (sclp1-to-sint8 value))
      (implies
       (sclp1-is-sint8-p value)
       (equal
        (sclp1-to-sint8 value)
        value))
      (equal
       (sclp1-to-sint8
        (sclp1-to-sint8 value))
       (sclp1-to-sint8 value))))))

(defun-sk sclp1-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sclp1-is-uint64-p
       (sclp1-to-uint64 value))
      (implies
       (sclp1-is-uint64-p value)
       (equal
        (sclp1-to-uint64 value)
        value))
      (equal
       (sclp1-to-uint64
        (sclp1-to-uint64 value))
       (sclp1-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sclp1-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sclp1-address-base address))
    (<= 0
        (sclp1-address-offset address))
    (<=
     (+ (sclp1-address-offset address)
        length)
     (sclp1-allocation
      (sclp1-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk sclp1-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sclp1-is-sint8-p
       (sclp1-character-memory
        (sclp1-shift address position)))))))

(defun-sk sclp1-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sclp1-character-memory
       (sclp1-shift address index))
      0)
     (sclp1-is-uint64-p index)
     (sclp1-valid-rw-p
      (sclp1-shift address 0)
      (+ 1 index))
     (sclp1-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sclp1-strlen-laws-p ()
  (forall (address)
    (implies
     (sclp1-address-p address)
     (and
      (if
          (equal
           (sclp1-character-memory
            (sclp1-shift address 0))
           0)
          (equal
           (sclp1-l-strlen address)
           0)
        (equal
         (sclp1-to-uint64
          (+ 1
             (sclp1-l-strlen
              (sclp1-shift address 1))))
         (sclp1-l-strlen address)))
      (sclp1-is-uint64-p
       (sclp1-l-strlen address))))))

;; Exact universal closure of A_Strchr.fix_l_strchr.

(defun-sk sclp1-strchr-law-p ()
  (forall (address value)
    (implies
     (and
      (sclp1-address-p address)
      (integerp value))
     (if
         (equal
          (sclp1-character-memory address)
          value)
         (equal
          (sclp1-l-strchr address value)
          address)
       (if
           (equal
            (sclp1-character-memory address)
            0)
           (equal
            (sclp1-l-strchr address value)
            (sclp1-null-address))
         (equal
          (sclp1-l-strchr
           (sclp1-shift address 1)
           value)
          (sclp1-l-strchr address value)))))))

;; The final source hypothesis retains its universal quantifier over every
;; address rather than exposing a witness or restricting the carrier.

(defun-sk sclp1-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (sclp1-address-p candidate)
     (implies
      (sclp1-addr-lt-p candidate current)
      (implies
       (sclp1-addr-le-p start candidate)
       (not
        (equal
         (sclp1-character-memory candidate)
         value)))))))

(defun-sk
    ntp4vc-strchr-loop-inv-preserved-goal1-statement ()
  (forall
   (a i a1)
   (implies
    (and
     (sclp1-address-p a)
     (integerp i)
     (sclp1-address-p a1)
     (sclp1-function-types-p)
     (sclp1-address-order-laws-p)
     (sclp1-to-sint8-laws-p)
     (sclp1-to-uint64-laws-p)
     (sclp1-strlen-laws-p)
     (sclp1-strchr-law-p))
    (let*
        ((x
          (sclp1-character-memory a))
         (x1
          (sclp1-to-sint8 i)))
      (implies
       (and
        (not (equal x 0))
        (not (equal x x1))
        (equal
         (sclp1-l-strchr a1 x1)
         (sclp1-l-strchr a x1))
        (<=
         (sclp1-region
          (sclp1-address-base a1))
         0)
        (sclp1-linked-p)
        (sclp1-sconst-p)
        (sclp1-is-sint32-p i)
        (sclp1-addr-le-p a1 a)
        (sclp1-is-sint8-p x)
        (sclp1-valid-string-p a)
        (sclp1-valid-string-p a1)
        (sclp1-addr-le-p
         a
         (sclp1-shift
          a1
          (sclp1-l-strlen a1)))
        (sclp1-no-earlier-match-p
         a1 a x1))
       (sclp1-valid-string-p
        (sclp1-shift a 1)))))))

(value-triple :itpeval-statement-checked)

:q
