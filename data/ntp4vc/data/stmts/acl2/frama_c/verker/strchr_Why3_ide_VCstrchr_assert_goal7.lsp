;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchr_Why3_ide_VCstrchr_assert_goal7:
;; an address precedes the valid C string endpoint exactly when the searched
;; signed byte is nonzero, under the stated strchr, address-order,
;; memory-validity, linkedness, constancy, and no-earlier-match hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun scg7-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun scg7-address-base (address)
  (car address))

(defun scg7-address-offset (address)
  (cdr address))

(defun scg7-shift (address amount)
  (cons
   (scg7-address-base address)
   (+ (scg7-address-offset address) amount)))

(defun scg7-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchr, C integer conversion,
;; linkedness, and constancy symbols.

(defstub scg7-character-memory (address) t)
(defstub scg7-allocation (index) t)
(defstub scg7-region (base) t)
(defstub scg7-addr-le-op (left right) t)
(defstub scg7-addr-lt-op (left right) t)
(defstub scg7-l-strlen (address) t)
(defstub scg7-l-strchr (address value) t)
(defstub scg7-to-uint8 (value) t)
(defstub scg7-to-sint8 (value) t)
(defstub scg7-to-uint64 (value) t)
(defstub scg7-to-sint64 (value) t)
(defstub scg7-linked-op () t)
(defstub scg7-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk scg7-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (scg7-address-p address)
      (and
       (integerp (scg7-character-memory address))
       (integerp (scg7-l-strlen address))))
     (implies
      (integerp index)
      (integerp (scg7-allocation index)))
     (implies
      (integerp base)
      (integerp (scg7-region base)))
     (implies
      (integerp value)
      (and
       (integerp (scg7-to-uint8 value))
       (integerp (scg7-to-sint8 value))
       (integerp (scg7-to-uint64 value))
       (integerp (scg7-to-sint64 value))))
     (implies
      (and
       (scg7-address-p address)
       (integerp value))
      (scg7-address-p
       (scg7-l-strchr address value))))))

(defun scg7-addr-le-p (left right)
  (if (scg7-addr-le-op left right) t nil))

(defun scg7-addr-lt-p (left right)
  (if (scg7-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; integer order on offsets.

(defun-sk scg7-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (scg7-address-p left)
      (scg7-address-p right)
      (equal
       (scg7-address-base left)
       (scg7-address-base right)))
     (and
      (equal
       (scg7-addr-le-p left right)
       (<=
        (scg7-address-offset left)
        (scg7-address-offset right)))
      (equal
       (scg7-addr-lt-p left right)
       (<
        (scg7-address-offset left)
        (scg7-address-offset right)))))))

(defun scg7-linked-p ()
  (if (scg7-linked-op) t nil))

(defun scg7-sconst-p ()
  (if (scg7-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun scg7-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun scg7-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun scg7-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun scg7-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun scg7-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by the VC and its logical string recurrences.

(defun-sk scg7-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg7-is-uint8-p
       (scg7-to-uint8 value))
      (implies
       (scg7-is-uint8-p value)
       (equal
        (scg7-to-uint8 value)
        value))
      (equal
       (scg7-to-uint8
        (scg7-to-uint8 value))
       (scg7-to-uint8 value))))))

(defun-sk scg7-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg7-is-sint8-p
       (scg7-to-sint8 value))
      (implies
       (scg7-is-sint8-p value)
       (equal
        (scg7-to-sint8 value)
        value))
      (equal
       (scg7-to-sint8
        (scg7-to-sint8 value))
       (scg7-to-sint8 value))))))

(defun-sk scg7-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg7-is-uint64-p
       (scg7-to-uint64 value))
      (implies
       (scg7-is-uint64-p value)
       (equal
        (scg7-to-uint64 value)
        value))
      (equal
       (scg7-to-uint64
        (scg7-to-uint64 value))
       (scg7-to-uint64 value))))))

(defun-sk scg7-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg7-is-sint64-p
       (scg7-to-sint64 value))
      (implies
       (scg7-is-sint64-p value)
       (equal
        (scg7-to-sint64 value)
        value))
      (equal
       (scg7-to-sint64
        (scg7-to-sint64 value))
       (scg7-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk scg7-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (scg7-to-sint8
        (scg7-to-uint8 value))
       (scg7-to-sint8 value))
      (equal
       (scg7-to-sint64
        (scg7-to-uint64 value))
       (scg7-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun scg7-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (scg7-address-base address))
    (<= 0
        (scg7-address-offset address))
    (<=
     (+ (scg7-address-offset address)
        length)
     (scg7-allocation
      (scg7-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk scg7-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (scg7-is-sint8-p
       (scg7-character-memory
        (scg7-shift address position)))))))

(defun-sk scg7-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (scg7-character-memory
       (scg7-shift address index))
      0)
     (scg7-is-uint64-p index)
     (scg7-valid-rw-p
      (scg7-shift address 0)
      (+ 1 index))
     (scg7-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk scg7-strlen-laws-p ()
  (forall (address)
    (implies
     (scg7-address-p address)
     (and
      (if
          (equal
           (scg7-character-memory
            (scg7-shift address 0))
           0)
          (equal
           (scg7-l-strlen address)
           0)
        (equal
         (scg7-to-uint64
          (+ 1
             (scg7-l-strlen
              (scg7-shift address 1))))
         (scg7-l-strlen address)))
      (scg7-is-uint64-p
       (scg7-l-strlen address))))))

;; Exact universal closure of A_Strchr.fix_l_strchr.

(defun-sk scg7-strchr-law-p ()
  (forall (address value)
    (implies
     (and
      (scg7-address-p address)
      (integerp value))
     (if
         (equal
          (scg7-character-memory address)
          value)
         (equal
          (scg7-l-strchr address value)
          address)
       (if
           (equal
            (scg7-character-memory address)
            0)
           (equal
            (scg7-l-strchr address value)
            (scg7-null-address))
         (equal
          (scg7-l-strchr
           (scg7-shift address 1)
           value)
          (scg7-l-strchr address value)))))))

;; The final source hypothesis retains its universal quantifier over every
;; address rather than exposing a witness or restricting the carrier.

(defun-sk scg7-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (scg7-address-p candidate)
     (implies
      (scg7-addr-lt-p candidate current)
      (implies
       (scg7-addr-le-p start candidate)
       (not
        (equal
         value
         (scg7-character-memory candidate))))))))

(defun-sk ntp4vc-strchr-assert-goal7-statement ()
  (forall
   (a a1 i)
   (implies
    (and
     (scg7-address-p a)
     (scg7-address-p a1)
     (integerp i)
     (scg7-function-types-p)
     (scg7-address-order-laws-p)
     (scg7-to-uint8-laws-p)
     (scg7-to-sint8-laws-p)
     (scg7-to-uint64-laws-p)
     (scg7-to-sint64-laws-p)
     (scg7-signed-unsigned-projection-laws-p)
     (scg7-strlen-laws-p)
     (scg7-strchr-law-p))
    (let*
        ((x
          (scg7-character-memory a))
         (a2
          (scg7-shift
           a1
           (scg7-l-strlen a1))))
      (implies
       (and
        (equal
         x
         (scg7-to-sint8 i))
        (equal
         (scg7-l-strchr a1 x)
         (scg7-l-strchr a x))
        (<=
         (scg7-region
          (scg7-address-base a1))
         0)
        (scg7-linked-p)
        (scg7-sconst-p)
        (scg7-is-sint32-p i)
        (scg7-addr-le-p a1 a)
        (scg7-is-sint8-p x)
        (scg7-valid-string-p a)
        (scg7-valid-string-p a1)
        (scg7-addr-le-p a a2)
        (scg7-no-earlier-match-p
         a1 a x))
       (equal
        (scg7-addr-lt-p a a2)
        (not (equal x 0))))))))

(value-triple :itpeval-statement-checked)

:q
