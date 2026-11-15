;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchr_Why3_ide_VCstrchr_loop_term_positive_goal9:
;; the current address offset does not exceed the valid string's logical
;; endpoint, under the stated character, strchr-result, address-order,
;; linkedness, constancy, string-validity, and no-earlier-match hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sctg9-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sctg9-address-base (address)
  (car address))

(defun sctg9-address-offset (address)
  (cdr address))

(defun sctg9-shift (address amount)
  (cons
   (sctg9-address-base address)
   (+ (sctg9-address-offset address) amount)))

(defun sctg9-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchr, C integer conversion,
;; linkedness, and constancy symbols.

(defstub sctg9-character-memory (address) t)
(defstub sctg9-allocation (index) t)
(defstub sctg9-region (base) t)
(defstub sctg9-addr-le-op (left right) t)
(defstub sctg9-addr-lt-op (left right) t)
(defstub sctg9-l-strlen (address) t)
(defstub sctg9-l-strchr (address value) t)
(defstub sctg9-to-uint8 (value) t)
(defstub sctg9-to-sint8 (value) t)
(defstub sctg9-to-uint64 (value) t)
(defstub sctg9-to-sint64 (value) t)
(defstub sctg9-linked-op () t)
(defstub sctg9-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sctg9-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (sctg9-address-p address)
      (and
       (integerp
        (sctg9-character-memory address))
       (integerp
        (sctg9-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (sctg9-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sctg9-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (sctg9-to-uint8 value))
       (integerp
        (sctg9-to-sint8 value))
       (integerp
        (sctg9-to-uint64 value))
       (integerp
        (sctg9-to-sint64 value))))
     (implies
      (and
       (sctg9-address-p address)
       (integerp value))
      (sctg9-address-p
       (sctg9-l-strchr address value))))))

(defun sctg9-addr-le-p (left right)
  (if (sctg9-addr-le-op left right) t nil))

(defun sctg9-addr-lt-p (left right)
  (if (sctg9-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; integer order on offsets.

(defun-sk sctg9-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (sctg9-address-p left)
      (sctg9-address-p right)
      (equal
       (sctg9-address-base left)
       (sctg9-address-base right)))
     (and
      (equal
       (sctg9-addr-le-p left right)
       (<=
        (sctg9-address-offset left)
        (sctg9-address-offset right)))
      (equal
       (sctg9-addr-lt-p left right)
       (<
        (sctg9-address-offset left)
        (sctg9-address-offset right)))))))

(defun sctg9-linked-p ()
  (if (sctg9-linked-op) t nil))

(defun sctg9-sconst-p ()
  (if (sctg9-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sctg9-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sctg9-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun sctg9-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun sctg9-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun sctg9-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by this VC and its logical string recurrence.

(defun-sk sctg9-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sctg9-is-uint8-p
       (sctg9-to-uint8 value))
      (implies
       (sctg9-is-uint8-p value)
       (equal
        (sctg9-to-uint8 value)
        value))
      (equal
       (sctg9-to-uint8
        (sctg9-to-uint8 value))
       (sctg9-to-uint8 value))))))

(defun-sk sctg9-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sctg9-is-sint8-p
       (sctg9-to-sint8 value))
      (implies
       (sctg9-is-sint8-p value)
       (equal
        (sctg9-to-sint8 value)
        value))
      (equal
       (sctg9-to-sint8
        (sctg9-to-sint8 value))
       (sctg9-to-sint8 value))))))

(defun-sk sctg9-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sctg9-is-uint64-p
       (sctg9-to-uint64 value))
      (implies
       (sctg9-is-uint64-p value)
       (equal
        (sctg9-to-uint64 value)
        value))
      (equal
       (sctg9-to-uint64
        (sctg9-to-uint64 value))
       (sctg9-to-uint64 value))))))

(defun-sk sctg9-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sctg9-is-sint64-p
       (sctg9-to-sint64 value))
      (implies
       (sctg9-is-sint64-p value)
       (equal
        (sctg9-to-sint64 value)
        value))
      (equal
       (sctg9-to-sint64
        (sctg9-to-sint64 value))
       (sctg9-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk sctg9-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (sctg9-to-sint8
        (sctg9-to-uint8 value))
       (sctg9-to-sint8 value))
      (equal
       (sctg9-to-sint64
        (sctg9-to-uint64 value))
       (sctg9-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sctg9-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sctg9-address-base address))
    (<= 0
        (sctg9-address-offset address))
    (<=
     (+ (sctg9-address-offset address)
        length)
     (sctg9-allocation
      (sctg9-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk sctg9-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sctg9-is-sint8-p
       (sctg9-character-memory
        (sctg9-shift address position)))))))

(defun-sk sctg9-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sctg9-character-memory
       (sctg9-shift address index))
      0)
     (sctg9-is-uint64-p index)
     (sctg9-valid-rw-p
      (sctg9-shift address 0)
      (+ 1 index))
     (sctg9-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sctg9-strlen-laws-p ()
  (forall (address)
    (implies
     (sctg9-address-p address)
     (and
      (if
          (equal
           (sctg9-character-memory
            (sctg9-shift address 0))
           0)
          (equal
           (sctg9-l-strlen address)
           0)
        (equal
         (sctg9-to-uint64
          (+ 1
             (sctg9-l-strlen
              (sctg9-shift address 1))))
         (sctg9-l-strlen address)))
      (sctg9-is-uint64-p
       (sctg9-l-strlen address))))))

;; Exact universal closure of A_Strchr.fix_l_strchr.

(defun-sk sctg9-strchr-law-p ()
  (forall (address value)
    (implies
     (and
      (sctg9-address-p address)
      (integerp value))
     (if
         (equal
          (sctg9-character-memory address)
          value)
         (equal
          (sctg9-l-strchr address value)
          address)
       (if
           (equal
            (sctg9-character-memory address)
            0)
           (equal
            (sctg9-l-strchr address value)
            (sctg9-null-address))
         (equal
          (sctg9-l-strchr
           (sctg9-shift address 1)
           value)
          (sctg9-l-strchr address value)))))))

;; The final source hypothesis retains its universal quantifier over every
;; address rather than exposing a witness or restricting the carrier.

(defun-sk sctg9-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (sctg9-address-p candidate)
     (implies
      (sctg9-addr-lt-p candidate current)
      (implies
       (sctg9-addr-le-p start candidate)
       (not
        (equal
         (sctg9-character-memory candidate)
         value)))))))

(defun-sk
    ntp4vc-strchr-loop-term-positive-goal9-statement ()
  (forall
   (a i a1)
   (implies
    (and
     (sctg9-address-p a)
     (integerp i)
     (sctg9-address-p a1)
     (sctg9-function-types-p)
     (sctg9-address-order-laws-p)
     (sctg9-to-uint8-laws-p)
     (sctg9-to-sint8-laws-p)
     (sctg9-to-uint64-laws-p)
     (sctg9-to-sint64-laws-p)
     (sctg9-signed-unsigned-projection-laws-p)
     (sctg9-strlen-laws-p)
     (sctg9-strchr-law-p))
    (let*
        ((x
          (sctg9-character-memory a))
         (x1
          (sctg9-to-sint8 i))
         (x2
          (sctg9-l-strlen a1)))
      (implies
       (and
        (not (equal x 0))
        (not (equal x x1))
        (equal
         (sctg9-l-strchr a1 x1)
         (sctg9-l-strchr a x1))
        (<=
         (sctg9-region
          (sctg9-address-base a1))
         0)
        (sctg9-linked-p)
        (sctg9-sconst-p)
        (sctg9-is-sint32-p i)
        (sctg9-addr-le-p a1 a)
        (sctg9-is-sint8-p x)
        (sctg9-valid-string-p a)
        (sctg9-valid-string-p a1)
        (sctg9-addr-le-p
         a
         (sctg9-shift
          a1
          x2))
        (sctg9-no-earlier-match-p
         a1 a x1))
       (<=
        (sctg9-address-offset a)
        (+
         (sctg9-address-offset a1)
         x2)))))))

(value-triple :itpeval-statement-checked)

:q
