;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strspn_Why3_ide_VCstrspn_post_3_goal1:
;; the strspn postcondition that the character at a constrained source address
;; occurs in the accept string, under the stated memory, address-order,
;; valid-string, span, conditional branch, and quantified prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sp3g1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sp3g1-address-base (address)
  (car address))

(defun sp3g1-address-offset (address)
  (cdr address))

(defun sp3g1-shift (address amount)
  (cons
   (sp3g1-address-base address)
   (+ (sp3g1-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strspn, unsigned conversion,
;; linkedness, and constancy symbols.

(defstub sp3g1-character-memory (address) t)
(defstub sp3g1-allocation (index) t)
(defstub sp3g1-region (base) t)
(defstub sp3g1-addr-le-op (left right) t)
(defstub sp3g1-addr-lt-op (left right) t)
(defstub sp3g1-l-strlen (address) t)
(defstub sp3g1-l-strspn (string accept) t)
(defstub sp3g1-to-uint64 (value) t)
(defstub sp3g1-linked-op () t)
(defstub sp3g1-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sp3g1-function-types-p ()
  (forall (address other index base value)
    (and
     (implies
      (sp3g1-address-p address)
      (and
       (integerp
        (sp3g1-character-memory address))
       (integerp
        (sp3g1-l-strlen address))))
     (implies
      (and
       (sp3g1-address-p address)
       (sp3g1-address-p other))
      (integerp
       (sp3g1-l-strspn address other)))
     (implies
      (integerp index)
      (integerp
       (sp3g1-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sp3g1-region base)))
     (implies
      (integerp value)
      (integerp
       (sp3g1-to-uint64 value))))))

(defun sp3g1-addr-le-p (left right)
  (if (sp3g1-addr-le-op left right) t nil))

(defun sp3g1-addr-lt-p (left right)
  (if (sp3g1-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk sp3g1-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (sp3g1-address-p left)
      (sp3g1-address-p right)
      (equal
       (sp3g1-address-base left)
       (sp3g1-address-base right)))
     (and
      (equal
       (sp3g1-addr-le-p left right)
       (<=
        (sp3g1-address-offset left)
        (sp3g1-address-offset right)))
      (equal
       (sp3g1-addr-lt-p left right)
       (<
        (sp3g1-address-offset left)
        (sp3g1-address-offset right)))))))

(defun sp3g1-linked-p ()
  (if (sp3g1-linked-op) t nil))

(defun sp3g1-sconst-p ()
  (if (sp3g1-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sp3g1-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sp3g1-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation used by logical strlen.

(defun-sk sp3g1-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sp3g1-is-uint64-p
       (sp3g1-to-uint64 value))
      (implies
       (sp3g1-is-uint64-p value)
       (equal
        (sp3g1-to-uint64 value)
        value))
      (equal
       (sp3g1-to-uint64
        (sp3g1-to-uint64 value))
       (sp3g1-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun sp3g1-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sp3g1-address-base address))
    (<= 0
        (sp3g1-address-offset address))
    (<=
     (+ (sp3g1-address-offset address)
        length)
     (sp3g1-allocation
      (sp3g1-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk sp3g1-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sp3g1-is-sint8-p
       (sp3g1-character-memory
        (sp3g1-shift address position)))))))

(defun-sk sp3g1-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sp3g1-character-memory
       (sp3g1-shift address index))
      0)
     (sp3g1-is-uint64-p index)
     (sp3g1-valid-rw-p
      (sp3g1-shift address 0)
      (+ 1 index))
     (sp3g1-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sp3g1-strlen-laws-p ()
  (forall (address)
    (implies
     (sp3g1-address-p address)
     (and
      (if
          (equal
           (sp3g1-character-memory
            (sp3g1-shift address 0))
           0)
          (equal
           (sp3g1-l-strlen address)
           0)
        (equal
         (sp3g1-to-uint64
          (+ 1
             (sp3g1-l-strlen
              (sp3g1-shift address 1))))
         (sp3g1-l-strlen address)))
      (sp3g1-is-uint64-p
       (sp3g1-l-strlen address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk sp3g1-in-array-p (start value)
  (exists (candidate)
    (and
     (sp3g1-address-p candidate)
     (equal
      (sp3g1-character-memory candidate)
      value)
     (sp3g1-addr-le-p start candidate)
     (sp3g1-addr-lt-p
      candidate
      (sp3g1-shift
       start
       (sp3g1-l-strlen start))))))

;; Exact universal closures of the three A_StrSpn axioms.

(defun-sk sp3g1-strspn-laws-p ()
  (forall (string accept)
    (implies
     (and
      (sp3g1-address-p string)
      (sp3g1-address-p accept))
     (and
      (implies
       (equal
        (sp3g1-character-memory string)
        0)
       (equal
        (sp3g1-l-strspn string accept)
        0))
      (implies
       (and
        (not
         (equal
          (sp3g1-character-memory string)
          0))
        (not
         (sp3g1-in-array-p
          accept
          (sp3g1-character-memory string))))
       (equal
        (sp3g1-l-strspn string accept)
        0))
      (implies
       (and
        (not
         (equal
          (sp3g1-character-memory string)
          0))
        (sp3g1-in-array-p
         accept
         (sp3g1-character-memory string)))
       (equal
        (+ 1
           (sp3g1-l-strspn
            (sp3g1-shift string 1)
            accept))
        (sp3g1-l-strspn string accept)))))))

;; The conditional branch's no-match hypothesis remains universal over every
;; address in the relevant accept-string prefix.

(defun-sk sp3g1-no-match-before-p
    (start current value)
  (forall (candidate)
    (implies
     (sp3g1-address-p candidate)
     (implies
      (sp3g1-addr-lt-p candidate current)
      (implies
       (sp3g1-addr-le-p start candidate)
       (not
        (equal
         value
         (sp3g1-character-memory candidate))))))))

;; For each source-prefix address, the matching accept-string address remains
;; an internal existential over the full address type.

(defun-sk sp3g1-accept-witness-p
    (source-candidate accept-start accept-end)
  (exists (accept-candidate)
    (and
     (sp3g1-address-p accept-candidate)
     (equal
      (sp3g1-character-memory source-candidate)
      (sp3g1-character-memory accept-candidate))
     (sp3g1-addr-le-p
      accept-start
      accept-candidate)
     (sp3g1-addr-lt-p
      accept-candidate
      accept-end))))

(defun-sk sp3g1-prefix-values-in-accept-p
    (source-start source-current accept-start accept-end)
  (forall (source-candidate)
    (implies
     (sp3g1-address-p source-candidate)
     (implies
      (sp3g1-addr-lt-p
       source-candidate
       source-current)
      (implies
       (sp3g1-addr-le-p
        source-start
        source-candidate)
       (sp3g1-accept-witness-p
        source-candidate
        accept-start
        accept-end))))))

(defun-sk ntp4vc-strspn-post-3-goal1-statement ()
  (forall
   (a1 a a2 a3 i a5 i1 i2 a4)
   (implies
    (and
     (sp3g1-address-p a1)
     (sp3g1-address-p a)
     (sp3g1-address-p a2)
     (sp3g1-address-p a3)
     (integerp i)
     (sp3g1-address-p a5)
     (integerp i1)
     (integerp i2)
     (sp3g1-address-p a4)
     (sp3g1-function-types-p)
     (sp3g1-address-order-laws-p)
     (sp3g1-to-uint64-laws-p)
     (sp3g1-strlen-laws-p)
     (sp3g1-strspn-laws-p))
    (let*
        ((x
          (sp3g1-address-offset a1))
         (x1
          (sp3g1-address-offset a))
         (x2
          (sp3g1-l-strlen a))
         (x3
          (sp3g1-character-memory a1))
         (x4
          (sp3g1-character-memory a2))
         (a6
          (sp3g1-shift
           a3
           (sp3g1-l-strlen a3))))
      (implies
       (and
        (equal
         (+ x
            (sp3g1-l-strspn a1 a3))
         (+ x1
            (sp3g1-l-strspn a a3)))
        (<= x1 x)
        (<=
         (sp3g1-region
          (sp3g1-address-base a))
         0)
        (<=
         (sp3g1-region
          (sp3g1-address-base a3))
         0)
        (<= x (+ x1 x2))
        (sp3g1-linked-p)
        (sp3g1-sconst-p)
        (sp3g1-is-uint64-p i)
        (sp3g1-addr-le-p a a1)
        (sp3g1-addr-le-p a a5)
        (sp3g1-is-sint8-p x3)
        (sp3g1-is-sint8-p x4)
        (sp3g1-valid-string-p a)
        (sp3g1-valid-string-p a1)
        (sp3g1-valid-string-p a3)
        (sp3g1-addr-lt-p
         a5
         (sp3g1-shift a i))
        (sp3g1-is-uint64-p (- x x1))
        (sp3g1-addr-le-p
         a1
         (sp3g1-shift a x2))
        (if
            (equal x3 0)
            (and
             (equal i1 i)
             (equal (+ i1 x1) x))
          (and
           (equal a2 a1)
           (equal i2 i)
           (equal
            (sp3g1-character-memory a4)
            0)
           (equal
            (+ i2 x1)
            (sp3g1-address-offset a2))
           (sp3g1-addr-le-p a3 a4)
           (sp3g1-valid-string-p a4)
           (not
            (sp3g1-in-array-p a3 x4))
           (sp3g1-addr-le-p a4 a6)
           (sp3g1-no-match-before-p
            a3 a4 x4)))
        (sp3g1-prefix-values-in-accept-p
         a a1 a3 a6))
       (sp3g1-accept-witness-p
        a5 a3 a6))))))

(value-triple :itpeval-statement-checked)

:q
