;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchr_Why3_ide_VCstrchr_exists_post_2_goal11:
;; the character at the candidate address equals the searched signed byte
;; under the stated strchr, address-order, valid-string, endpoint, linkedness,
;; constancy, and no-earlier-match hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun scg11-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun scg11-address-base (address)
  (car address))

(defun scg11-address-offset (address)
  (cdr address))

(defun scg11-shift (address amount)
  (cons
   (scg11-address-base address)
   (+ (scg11-address-offset address) amount)))

(defun scg11-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchr, C integer conversion,
;; linkedness, and constancy symbols.

(defstub scg11-character-memory (address) t)
(defstub scg11-allocation (index) t)
(defstub scg11-region (base) t)
(defstub scg11-addr-le-op (left right) t)
(defstub scg11-addr-lt-op (left right) t)
(defstub scg11-l-strlen (address) t)
(defstub scg11-l-strchr (address value) t)
(defstub scg11-to-uint8 (value) t)
(defstub scg11-to-sint8 (value) t)
(defstub scg11-to-uint64 (value) t)
(defstub scg11-to-sint64 (value) t)
(defstub scg11-linked-op () t)
(defstub scg11-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk scg11-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (scg11-address-p address)
      (and
       (integerp
        (scg11-character-memory address))
       (integerp
        (scg11-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (scg11-allocation index)))
     (implies
      (integerp base)
      (integerp
       (scg11-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (scg11-to-uint8 value))
       (integerp
        (scg11-to-sint8 value))
       (integerp
        (scg11-to-uint64 value))
       (integerp
        (scg11-to-sint64 value))))
     (implies
      (and
       (scg11-address-p address)
       (integerp value))
      (scg11-address-p
       (scg11-l-strchr address value))))))

(defun scg11-addr-le-p (left right)
  (if (scg11-addr-le-op left right) t nil))

(defun scg11-addr-lt-p (left right)
  (if (scg11-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; integer order on offsets.

(defun-sk scg11-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (scg11-address-p left)
      (scg11-address-p right)
      (equal
       (scg11-address-base left)
       (scg11-address-base right)))
     (and
      (equal
       (scg11-addr-le-p left right)
       (<=
        (scg11-address-offset left)
        (scg11-address-offset right)))
      (equal
       (scg11-addr-lt-p left right)
       (<
        (scg11-address-offset left)
        (scg11-address-offset right)))))))

(defun scg11-linked-p ()
  (if (scg11-linked-op) t nil))

(defun scg11-sconst-p ()
  (if (scg11-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun scg11-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun scg11-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun scg11-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun scg11-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun scg11-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by the VC and its logical string recurrences.

(defun-sk scg11-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg11-is-uint8-p
       (scg11-to-uint8 value))
      (implies
       (scg11-is-uint8-p value)
       (equal
        (scg11-to-uint8 value)
        value))
      (equal
       (scg11-to-uint8
        (scg11-to-uint8 value))
       (scg11-to-uint8 value))))))

(defun-sk scg11-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg11-is-sint8-p
       (scg11-to-sint8 value))
      (implies
       (scg11-is-sint8-p value)
       (equal
        (scg11-to-sint8 value)
        value))
      (equal
       (scg11-to-sint8
        (scg11-to-sint8 value))
       (scg11-to-sint8 value))))))

(defun-sk scg11-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg11-is-uint64-p
       (scg11-to-uint64 value))
      (implies
       (scg11-is-uint64-p value)
       (equal
        (scg11-to-uint64 value)
        value))
      (equal
       (scg11-to-uint64
        (scg11-to-uint64 value))
       (scg11-to-uint64 value))))))

(defun-sk scg11-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg11-is-sint64-p
       (scg11-to-sint64 value))
      (implies
       (scg11-is-sint64-p value)
       (equal
        (scg11-to-sint64 value)
        value))
      (equal
       (scg11-to-sint64
        (scg11-to-sint64 value))
       (scg11-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk scg11-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (scg11-to-sint8
        (scg11-to-uint8 value))
       (scg11-to-sint8 value))
      (equal
       (scg11-to-sint64
        (scg11-to-uint64 value))
       (scg11-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun scg11-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (scg11-address-base address))
    (<= 0
        (scg11-address-offset address))
    (<=
     (+ (scg11-address-offset address)
        length)
     (scg11-allocation
      (scg11-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk scg11-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (scg11-is-sint8-p
       (scg11-character-memory
        (scg11-shift address position)))))))

(defun-sk scg11-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (scg11-character-memory
       (scg11-shift address index))
      0)
     (scg11-is-uint64-p index)
     (scg11-valid-rw-p
      (scg11-shift address 0)
      (+ 1 index))
     (scg11-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk scg11-strlen-laws-p ()
  (forall (address)
    (implies
     (scg11-address-p address)
     (and
      (if
          (equal
           (scg11-character-memory
            (scg11-shift address 0))
           0)
          (equal
           (scg11-l-strlen address)
           0)
        (equal
         (scg11-to-uint64
          (+ 1
             (scg11-l-strlen
              (scg11-shift address 1))))
         (scg11-l-strlen address)))
      (scg11-is-uint64-p
       (scg11-l-strlen address))))))

;; Exact universal closure of A_Strchr.fix_l_strchr.

(defun-sk scg11-strchr-law-p ()
  (forall (address value)
    (implies
     (and
      (scg11-address-p address)
      (integerp value))
     (if
         (equal
          (scg11-character-memory address)
          value)
         (equal
          (scg11-l-strchr address value)
          address)
       (if
           (equal
            (scg11-character-memory address)
            0)
           (equal
            (scg11-l-strchr address value)
            (scg11-null-address))
         (equal
          (scg11-l-strchr
           (scg11-shift address 1)
           value)
          (scg11-l-strchr address value)))))))

;; The final source hypothesis retains its universal quantifier over every
;; address rather than exposing a witness or restricting the carrier.

(defun-sk scg11-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (scg11-address-p candidate)
     (implies
      (scg11-addr-lt-p candidate current)
      (implies
       (scg11-addr-le-p start candidate)
       (not
        (equal
         value
         (scg11-character-memory candidate))))))))

(defun-sk ntp4vc-strchr-exists-post-2-goal11-statement ()
  (forall
   (a3 a a1 a2 i)
   (implies
    (and
     (scg11-address-p a3)
     (scg11-address-p a)
     (scg11-address-p a1)
     (scg11-address-p a2)
     (integerp i)
     (scg11-function-types-p)
     (scg11-address-order-laws-p)
     (scg11-to-uint8-laws-p)
     (scg11-to-sint8-laws-p)
     (scg11-to-uint64-laws-p)
     (scg11-to-sint64-laws-p)
     (scg11-signed-unsigned-projection-laws-p)
     (scg11-strlen-laws-p)
     (scg11-strchr-law-p))
    (let*
        ((x
          (scg11-character-memory a3))
         (x1
          (scg11-character-memory a))
         (x2
          (scg11-character-memory a1))
         (a4
          (scg11-shift
           a2
           (scg11-l-strlen a2))))
      (implies
       (and
        (equal
         x
         (scg11-to-sint8 i))
        (equal
         (scg11-l-strchr a2 x)
         (scg11-l-strchr a1 x))
        (<=
         (scg11-region
          (scg11-address-base a2))
         0)
        (scg11-linked-p)
        (scg11-sconst-p)
        (scg11-is-sint32-p i)
        (scg11-addr-le-p a2 a1)
        (scg11-addr-le-p a2 a3)
        (scg11-is-sint8-p x1)
        (scg11-is-sint8-p x2)
        (scg11-valid-string-p a1)
        (scg11-valid-string-p a2)
        (scg11-addr-le-p a1 a4)
        (scg11-addr-le-p a3 a4)
        (if
            (equal x x2)
            (and
             (equal a1 a)
             (equal
              (equal a4 a)
              (equal x1 0))
             (equal
              (scg11-addr-lt-p a a4)
              (not (equal x1 0))))
          (and
           (equal
            (scg11-null-address)
            a)
           (equal x2 0)))
        (scg11-no-earlier-match-p
         a2 a1 x))
       (equal x x1))))))

(value-triple :itpeval-statement-checked)

:q
