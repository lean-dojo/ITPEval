;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strspn_Why3_ide_VCstrspn_post_2_goal0:
;; the strspn postcondition that the character at the uint64 index differs
;; from the character at the current accept address, under the stated memory,
;; address-order, valid-string, span, and quantified prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sp2g0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sp2g0-address-base (address)
  (car address))

(defun sp2g0-address-offset (address)
  (cdr address))

(defun sp2g0-shift (address amount)
  (cons
   (sp2g0-address-base address)
   (+ (sp2g0-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strspn, unsigned conversion,
;; linkedness, and constancy symbols.

(defstub sp2g0-character-memory (address) t)
(defstub sp2g0-allocation (index) t)
(defstub sp2g0-region (base) t)
(defstub sp2g0-addr-le-op (left right) t)
(defstub sp2g0-addr-lt-op (left right) t)
(defstub sp2g0-l-strlen (address) t)
(defstub sp2g0-l-strspn (string accept) t)
(defstub sp2g0-to-uint64 (value) t)
(defstub sp2g0-linked-op () t)
(defstub sp2g0-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sp2g0-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (sp2g0-address-p address)
      (and
       (integerp
        (sp2g0-character-memory address))
       (integerp
        (sp2g0-l-strlen address))))
     (implies
      (and
       (sp2g0-address-p address)
       (sp2g0-address-p other))
      (integerp
       (sp2g0-l-strspn address other)))
     (implies
      (integerp index)
      (integerp
       (sp2g0-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sp2g0-region base)))
     (implies
      (integerp value)
      (integerp
       (sp2g0-to-uint64 value))))))

(defun sp2g0-addr-le-p (left right)
  (if (sp2g0-addr-le-op left right) t nil))

(defun sp2g0-addr-lt-p (left right)
  (if (sp2g0-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk sp2g0-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (sp2g0-address-p left)
      (sp2g0-address-p right)
      (equal
       (sp2g0-address-base left)
       (sp2g0-address-base right)))
     (and
      (equal
       (sp2g0-addr-le-p left right)
       (<=
        (sp2g0-address-offset left)
        (sp2g0-address-offset right)))
      (equal
       (sp2g0-addr-lt-p left right)
       (<
        (sp2g0-address-offset left)
        (sp2g0-address-offset right)))))))

(defun sp2g0-linked-p ()
  (if (sp2g0-linked-op) t nil))

(defun sp2g0-sconst-p ()
  (if (sp2g0-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sp2g0-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sp2g0-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation used by logical strlen.

(defun-sk sp2g0-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sp2g0-is-uint64-p
       (sp2g0-to-uint64 value))
      (implies
       (sp2g0-is-uint64-p value)
       (equal
        (sp2g0-to-uint64 value)
        value))
      (equal
       (sp2g0-to-uint64
        (sp2g0-to-uint64 value))
       (sp2g0-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sp2g0-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sp2g0-address-base address))
    (<= 0
        (sp2g0-address-offset address))
    (<=
     (+ (sp2g0-address-offset address)
        length)
     (sp2g0-allocation
      (sp2g0-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk sp2g0-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sp2g0-is-sint8-p
       (sp2g0-character-memory
        (sp2g0-shift address position)))))))

(defun-sk sp2g0-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sp2g0-character-memory
       (sp2g0-shift address index))
      0)
     (sp2g0-is-uint64-p index)
     (sp2g0-valid-rw-p
      (sp2g0-shift address 0)
      (+ 1 index))
     (sp2g0-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sp2g0-strlen-laws-p ()
  (forall (address)
    (implies
     (sp2g0-address-p address)
     (and
      (if
          (equal
           (sp2g0-character-memory
            (sp2g0-shift address 0))
           0)
          (equal
           (sp2g0-l-strlen address)
           0)
        (equal
         (sp2g0-to-uint64
          (+ 1
             (sp2g0-l-strlen
              (sp2g0-shift address 1))))
         (sp2g0-l-strlen address)))
      (sp2g0-is-uint64-p
       (sp2g0-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk sp2g0-in-array-p (start value)
  (exists (candidate)
    (and
     (sp2g0-address-p candidate)
     (equal
      (sp2g0-character-memory candidate)
      value)
     (sp2g0-addr-le-p start candidate)
     (sp2g0-addr-lt-p
      candidate
      (sp2g0-shift
       start
       (sp2g0-l-strlen start))))))

;; Exact universal closures of the three A_StrSpn axioms.

(defun-sk sp2g0-strspn-laws-p ()
  (forall (string accept)
    (implies
     (and
      (sp2g0-address-p string)
      (sp2g0-address-p accept))
     (and
      (implies
       (equal
        (sp2g0-character-memory string)
        0)
       (equal
        (sp2g0-l-strspn string accept)
        0))
      (implies
       (and
        (not
         (equal
          (sp2g0-character-memory string)
          0))
        (not
         (sp2g0-in-array-p
          accept
          (sp2g0-character-memory string))))
       (equal
        (sp2g0-l-strspn string accept)
        0))
      (implies
       (and
        (not
         (equal
          (sp2g0-character-memory string)
          0))
        (sp2g0-in-array-p
         accept
         (sp2g0-character-memory string)))
       (equal
        (+ 1
           (sp2g0-l-strspn
            (sp2g0-shift string 1)
            accept))
        (sp2g0-l-strspn string accept)))))))

;; The conditional branch's no-match hypothesis remains universal over every
;; address in the relevant accept-string prefix.

(defun-sk sp2g0-no-match-before-p
    (start current value)
  (forall (candidate)
    (implies
     (sp2g0-address-p candidate)
     (implies
      (sp2g0-addr-lt-p candidate current)
      (implies
       (sp2g0-addr-le-p start candidate)
       (not
        (equal
         value
         (sp2g0-character-memory candidate))))))))

;; For each source-prefix address, the matching accept-string address remains
;; an internal existential over the full address type.

(defun-sk sp2g0-accept-witness-p
    (source-candidate accept-start accept-end)
  (exists (accept-candidate)
    (and
     (sp2g0-address-p accept-candidate)
     (equal
      (sp2g0-character-memory source-candidate)
      (sp2g0-character-memory accept-candidate))
     (sp2g0-addr-le-p
      accept-start
      accept-candidate)
     (sp2g0-addr-lt-p
      accept-candidate
      accept-end))))

(defun-sk sp2g0-prefix-values-in-accept-p
    (source-start source-current accept-start accept-end)
  (forall (source-candidate)
    (implies
     (sp2g0-address-p source-candidate)
     (implies
      (sp2g0-addr-lt-p
       source-candidate
       source-current)
      (implies
       (sp2g0-addr-le-p
        source-start
        source-candidate)
       (sp2g0-accept-witness-p
        source-candidate
        accept-start
        accept-end))))))

(defun-sk ntp4vc-strspn-post-2-goal0-statement ()
  (forall
   (a1 a a2 a3 i a5 a4)
   (implies
    (and
     (sp2g0-address-p a1)
     (sp2g0-address-p a)
     (sp2g0-address-p a2)
     (sp2g0-address-p a3)
     (integerp i)
     (sp2g0-address-p a5)
     (sp2g0-address-p a4)
     (sp2g0-function-types-p)
     (sp2g0-address-order-laws-p)
     (sp2g0-to-uint64-laws-p)
     (sp2g0-strlen-laws-p)
     (sp2g0-strspn-laws-p))
    (let*
        ((x
          (sp2g0-address-offset a1))
         (x1
          (sp2g0-address-offset a))
         (x2
          (sp2g0-l-strlen a))
         (x3
          (sp2g0-character-memory a1))
         (x4
          (sp2g0-character-memory a2))
         (a6
          (sp2g0-shift
           a3
           (sp2g0-l-strlen a3)))
         (x5
          (+ i x1)))
      (implies
       (and
        (equal
         (+ x
            (sp2g0-l-strspn a1 a3))
         (+ x1
            (sp2g0-l-strspn a a3)))
        (<= x1 x)
        (<=
         (sp2g0-region
          (sp2g0-address-base a))
         0)
        (<=
         (sp2g0-region
          (sp2g0-address-base a3))
         0)
        (<= x (+ x1 x2))
        (sp2g0-linked-p)
        (sp2g0-sconst-p)
        (sp2g0-is-uint64-p i)
        (sp2g0-addr-le-p a a1)
        (sp2g0-addr-le-p a3 a5)
        (sp2g0-is-sint8-p x3)
        (sp2g0-is-sint8-p x4)
        (sp2g0-valid-string-p a)
        (sp2g0-valid-string-p a1)
        (sp2g0-valid-string-p a3)
        (sp2g0-is-uint64-p (- x x1))
        (sp2g0-addr-lt-p a5 a6)
        (sp2g0-addr-le-p
         a1
         (sp2g0-shift a x2))
        (if
            (equal x3 0)
            (equal x5 x)
          (and
           (equal a2 a1)
           (equal
            (sp2g0-character-memory a4)
            0)
           (equal
            x5
            (sp2g0-address-offset a2))
           (sp2g0-addr-le-p a3 a4)
           (sp2g0-valid-string-p a4)
           (not
            (sp2g0-in-array-p a3 x4))
           (sp2g0-addr-le-p a4 a6)
           (sp2g0-no-match-before-p
            a3 a4 x4)))
        (sp2g0-prefix-values-in-accept-p
         a a1 a3 a6))
       (not
        (equal
         (sp2g0-character-memory
          (sp2g0-shift a i))
         (sp2g0-character-memory a5))))))))

(value-triple :itpeval-statement-checked)

:q
