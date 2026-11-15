;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchr_Why3_ide_VCstrchr_exists_post_3_goal12:
;; the character at a constrained address differs from the searched signed
;; byte under the VC's strchr equality, address-order, valid-string, endpoint,
;; linkedness, constancy, conditional-address, and no-earlier-match hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun scg12-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun scg12-address-base (address)
  (car address))

(defun scg12-address-offset (address)
  (cdr address))

(defun scg12-shift (address amount)
  (cons
   (scg12-address-base address)
   (+ (scg12-address-offset address) amount)))

(defun scg12-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchr, C integer conversion,
;; linkedness, and constancy symbols.

(defstub scg12-character-memory (address) t)
(defstub scg12-allocation (index) t)
(defstub scg12-region (base) t)
(defstub scg12-addr-le-op (left right) t)
(defstub scg12-addr-lt-op (left right) t)
(defstub scg12-l-strlen (address) t)
(defstub scg12-l-strchr (address value) t)
(defstub scg12-to-uint8 (value) t)
(defstub scg12-to-sint8 (value) t)
(defstub scg12-to-uint64 (value) t)
(defstub scg12-to-sint64 (value) t)
(defstub scg12-linked-op () t)
(defstub scg12-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk scg12-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (scg12-address-p address)
      (and
       (integerp
        (scg12-character-memory address))
       (integerp
        (scg12-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (scg12-allocation index)))
     (implies
      (integerp base)
      (integerp
       (scg12-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (scg12-to-uint8 value))
       (integerp
        (scg12-to-sint8 value))
       (integerp
        (scg12-to-uint64 value))
       (integerp
        (scg12-to-sint64 value))))
     (implies
      (and
       (scg12-address-p address)
       (integerp value))
      (scg12-address-p
       (scg12-l-strchr address value))))))

(defun scg12-addr-le-p (left right)
  (if (scg12-addr-le-op left right) t nil))

(defun scg12-addr-lt-p (left right)
  (if (scg12-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; integer order on offsets.

(defun-sk scg12-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (scg12-address-p left)
      (scg12-address-p right)
      (equal
       (scg12-address-base left)
       (scg12-address-base right)))
     (and
      (equal
       (scg12-addr-le-p left right)
       (<=
        (scg12-address-offset left)
        (scg12-address-offset right)))
      (equal
       (scg12-addr-lt-p left right)
       (<
        (scg12-address-offset left)
        (scg12-address-offset right)))))))

(defun scg12-linked-p ()
  (if (scg12-linked-op) t nil))

(defun scg12-sconst-p ()
  (if (scg12-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun scg12-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun scg12-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun scg12-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun scg12-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun scg12-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by the VC and its logical string recurrences.

(defun-sk scg12-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg12-is-uint8-p
       (scg12-to-uint8 value))
      (implies
       (scg12-is-uint8-p value)
       (equal
        (scg12-to-uint8 value)
        value))
      (equal
       (scg12-to-uint8
        (scg12-to-uint8 value))
       (scg12-to-uint8 value))))))

(defun-sk scg12-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg12-is-sint8-p
       (scg12-to-sint8 value))
      (implies
       (scg12-is-sint8-p value)
       (equal
        (scg12-to-sint8 value)
        value))
      (equal
       (scg12-to-sint8
        (scg12-to-sint8 value))
       (scg12-to-sint8 value))))))

(defun-sk scg12-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg12-is-uint64-p
       (scg12-to-uint64 value))
      (implies
       (scg12-is-uint64-p value)
       (equal
        (scg12-to-uint64 value)
        value))
      (equal
       (scg12-to-uint64
        (scg12-to-uint64 value))
       (scg12-to-uint64 value))))))

(defun-sk scg12-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg12-is-sint64-p
       (scg12-to-sint64 value))
      (implies
       (scg12-is-sint64-p value)
       (equal
        (scg12-to-sint64 value)
        value))
      (equal
       (scg12-to-sint64
        (scg12-to-sint64 value))
       (scg12-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk scg12-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (scg12-to-sint8
        (scg12-to-uint8 value))
       (scg12-to-sint8 value))
      (equal
       (scg12-to-sint64
        (scg12-to-uint64 value))
       (scg12-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun scg12-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (scg12-address-base address))
    (<= 0
        (scg12-address-offset address))
    (<=
     (+ (scg12-address-offset address)
        length)
     (scg12-allocation
      (scg12-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk scg12-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (scg12-is-sint8-p
       (scg12-character-memory
        (scg12-shift address position)))))))

(defun-sk scg12-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (scg12-character-memory
       (scg12-shift address index))
      0)
     (scg12-is-uint64-p index)
     (scg12-valid-rw-p
      (scg12-shift address 0)
      (+ 1 index))
     (scg12-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk scg12-strlen-laws-p ()
  (forall (address)
    (implies
     (scg12-address-p address)
     (and
      (if
          (equal
           (scg12-character-memory
            (scg12-shift address 0))
           0)
          (equal
           (scg12-l-strlen address)
           0)
        (equal
         (scg12-to-uint64
          (+ 1
             (scg12-l-strlen
              (scg12-shift address 1))))
         (scg12-l-strlen address)))
      (scg12-is-uint64-p
       (scg12-l-strlen address))))))

;; Exact universal closure of A_Strchr.fix_l_strchr.

(defun-sk scg12-strchr-law-p ()
  (forall (address value)
    (implies
     (and
      (scg12-address-p address)
      (integerp value))
     (if
         (equal
          (scg12-character-memory address)
          value)
         (equal
          (scg12-l-strchr address value)
          address)
       (if
           (equal
            (scg12-character-memory address)
            0)
           (equal
            (scg12-l-strchr address value)
            (scg12-null-address))
         (equal
          (scg12-l-strchr
           (scg12-shift address 1)
           value)
          (scg12-l-strchr address value)))))))

;; The penultimate source hypothesis retains its universal quantifier over
;; every address rather than exposing a witness or restricting the carrier.

(defun-sk scg12-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (scg12-address-p candidate)
     (implies
      (scg12-addr-lt-p candidate current)
      (implies
       (scg12-addr-le-p start candidate)
       (not
        (equal
         value
         (scg12-character-memory candidate))))))))

(defun-sk ntp4vc-strchr-exists-post-3-goal12-statement ()
  (forall
   (a3 a a1 a2 i a4)
   (implies
    (and
     (scg12-address-p a3)
     (scg12-address-p a)
     (scg12-address-p a1)
     (scg12-address-p a2)
     (integerp i)
     (scg12-address-p a4)
     (scg12-function-types-p)
     (scg12-address-order-laws-p)
     (scg12-to-uint8-laws-p)
     (scg12-to-sint8-laws-p)
     (scg12-to-uint64-laws-p)
     (scg12-to-sint64-laws-p)
     (scg12-signed-unsigned-projection-laws-p)
     (scg12-strlen-laws-p)
     (scg12-strchr-law-p))
    (let*
        ((x
          (scg12-character-memory a3))
         (x1
          (scg12-character-memory a))
         (x2
          (scg12-character-memory a1))
         (a5
          (scg12-shift
           a2
           (scg12-l-strlen a2))))
      (implies
       (and
        (equal
         x
         (scg12-to-sint8 i))
        (equal
         (scg12-l-strchr a2 x)
         (scg12-l-strchr a x))
        (<=
         (scg12-region
          (scg12-address-base a2))
         0)
        (scg12-linked-p)
        (scg12-sconst-p)
        (scg12-is-sint32-p i)
        (scg12-addr-lt-p a4 a1)
        (scg12-addr-le-p a2 a)
        (scg12-addr-le-p a2 a3)
        (scg12-addr-le-p a2 a4)
        (scg12-is-sint8-p x1)
        (scg12-is-sint8-p x2)
        (scg12-valid-string-p a)
        (scg12-valid-string-p a2)
        (scg12-addr-le-p a a5)
        (scg12-addr-le-p a3 a5)
        (if
            (equal x x1)
            (and
             (equal a1 a)
             (equal
              (equal a5 a1)
              (equal x2 0))
             (equal
              (scg12-addr-lt-p a1 a5)
              (not (equal x2 0))))
          (and
           (equal
            (scg12-null-address)
            a1)
           (equal x1 0)))
        (scg12-no-earlier-match-p
         a2 a x))
       (not
        (equal
         (scg12-character-memory a4)
         x)))))))

(value-triple :itpeval-statement-checked)

:q
