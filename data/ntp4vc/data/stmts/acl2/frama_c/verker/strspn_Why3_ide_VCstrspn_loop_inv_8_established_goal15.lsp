;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strspn_Why3_ide_VCstrspn_loop_inv_8_established_goal15:
;; establishment of the strspn loop invariant that the byte at the constrained
;; accept-region address differs from the current source byte, under the stated
;; string, address-order, and quantified prefix-witness hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ssg15-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ssg15-address-base (address)
  (car address))

(defun ssg15-address-offset (address)
  (cdr address))

(defun ssg15-shift (address amount)
  (cons
   (ssg15-address-base address)
   (+ (ssg15-address-offset address)
      amount)))

;; A first-order function carrier and application symbol represent every
;; source character-memory function.  The theorem's t_1 is one universally
;; quantified carrier element.  Under the corrected A_StrSpn specification,
;; l_strspn takes that memory explicitly, so laws for different memories do
;; not constrain one shared result.

(defstub ssg15-character-memory (memory address) t)
(defstub ssg15-allocation (index) t)
(defstub ssg15-region (base) t)
(defstub ssg15-addr-le-op (left right) t)
(defstub ssg15-addr-lt-op (left right) t)
(defstub ssg15-l-strlen (memory address) t)
(defstub ssg15-l-strspn (memory string accept) t)
(defstub ssg15-to-uint64 (value) t)
(defstub ssg15-linked-op () t)
(defstub ssg15-sconst-op (memory) t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk ssg15-function-types-p ()
  (forall (memory address other index base value)
    (and
     (implies
      (ssg15-address-p address)
      (and
       (integerp
        (ssg15-character-memory memory address))
       (integerp
        (ssg15-l-strlen memory address))))
     (implies
      (and
       (ssg15-address-p address)
       (ssg15-address-p other))
      (integerp
       (ssg15-l-strspn memory address other)))
     (implies
      (integerp index)
      (integerp
       (ssg15-allocation index)))
     (implies
      (integerp base)
      (integerp
       (ssg15-region base)))
     (implies
      (integerp value)
      (integerp
       (ssg15-to-uint64 value))))))

(defun ssg15-addr-le-p (left right)
  (if (ssg15-addr-le-op left right) t nil))

(defun ssg15-addr-lt-p (left right)
  (if (ssg15-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk ssg15-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (ssg15-address-p left)
      (ssg15-address-p right)
      (equal
       (ssg15-address-base left)
       (ssg15-address-base right)))
     (and
      (equal
       (ssg15-addr-le-p left right)
       (<=
        (ssg15-address-offset left)
        (ssg15-address-offset right)))
      (equal
       (ssg15-addr-lt-p left right)
       (<
        (ssg15-address-offset left)
        (ssg15-address-offset right)))))))

(defun ssg15-linked-p ()
  (if (ssg15-linked-op) t nil))

(defun ssg15-sconst-p (memory)
  (if (ssg15-sconst-op memory) t nil))

;; Pointwise equality is source equality for character-memory functions.
;; The extensionality condition makes l_strlen and sconst well-defined on
;; those functions rather than on their first-order representatives.
;; Forward, each source function is represented by its carrier element and
;; pointwise application.  Conversely, each carrier element determines an
;; address-to-integer function; quotienting representatives by the equality
;; below recovers the source function sort, and extensionality makes every
;; operation used by this statement well-defined on that quotient.

(defun-sk ssg15-memories-equal-p (left-memory right-memory)
  (forall (address)
    (implies
     (ssg15-address-p address)
     (equal
      (ssg15-character-memory left-memory address)
      (ssg15-character-memory right-memory address)))))

(defun-sk ssg15-memory-extensionality-p ()
  (forall (left-memory right-memory address)
    (implies
     (and
      (ssg15-address-p address)
      (ssg15-memories-equal-p
       left-memory right-memory))
     (and
      (equal
       (ssg15-l-strlen left-memory address)
       (ssg15-l-strlen right-memory address))
      (equal
       (ssg15-sconst-p left-memory)
       (ssg15-sconst-p right-memory))))))

;; Exact mathematical ranges for the source C integer predicates.

(defun ssg15-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun ssg15-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation used by logical strlen.

(defun-sk ssg15-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ssg15-is-uint64-p
       (ssg15-to-uint64 value))
      (implies
       (ssg15-is-uint64-p value)
       (equal
        (ssg15-to-uint64 value)
        value))
      (equal
       (ssg15-to-uint64
        (ssg15-to-uint64 value))
       (ssg15-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun ssg15-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (ssg15-address-base address))
    (<= 0
        (ssg15-address-offset address))
    (<=
     (+ (ssg15-address-offset address)
        length)
     (ssg15-allocation
      (ssg15-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk ssg15-string-chars-sint8-through-p
    (memory address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (ssg15-is-sint8-p
       (ssg15-character-memory
        memory
        (ssg15-shift address position)))))))

(defun-sk ssg15-valid-string-p (memory address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (ssg15-character-memory
       memory
       (ssg15-shift address index))
      0)
     (ssg15-is-uint64-p index)
     (ssg15-valid-rw-p
      (ssg15-shift address 0)
      (+ 1 index))
     (ssg15-string-chars-sint8-through-p
      memory address index))))

;; Source-wide universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk ssg15-strlen-laws-p ()
  (forall (memory address)
    (implies
     (ssg15-address-p address)
     (and
      (if
          (equal
           (ssg15-character-memory
            memory
            (ssg15-shift address 0))
           0)
          (equal
           (ssg15-l-strlen memory address)
           0)
        (equal
         (ssg15-to-uint64
          (+ 1
             (ssg15-l-strlen
              memory
              (ssg15-shift address 1))))
         (ssg15-l-strlen memory address)))
      (ssg15-is-uint64-p
       (ssg15-l-strlen memory address))))))

;; Exact unfolding of A_StrSpn.p_in_array. Its witness remains existentially
;; quantified over the full source address type.

(defun-sk ssg15-in-array-p (memory start value)
  (exists (candidate)
    (and
     (ssg15-address-p candidate)
     (equal
      (ssg15-character-memory memory candidate)
      value)
     (ssg15-addr-le-p start candidate)
     (ssg15-addr-lt-p
      candidate
      (ssg15-shift
       start
       (ssg15-l-strlen memory start))))))

;; Exact source-wide universal closures of the corrected A_StrSpn axioms.
;; Every recursive equation uses the same explicit character memory.

(defun-sk ssg15-strspn-laws-p ()
  (forall (memory string accept)
    (implies
     (and
      (ssg15-address-p string)
      (ssg15-address-p accept))
     (and
      (implies
       (equal
        (ssg15-character-memory memory string)
        0)
       (equal
        (ssg15-l-strspn memory string accept)
        0))
      (implies
       (and
        (not
         (equal
          (ssg15-character-memory memory string)
          0))
        (not
         (ssg15-in-array-p
          memory
          accept
          (ssg15-character-memory memory string))))
       (equal
        (ssg15-l-strspn memory string accept)
        0))
      (implies
       (and
        (not
         (equal
          (ssg15-character-memory memory string)
          0))
        (ssg15-in-array-p
         memory
         accept
         (ssg15-character-memory memory string)))
       (equal
        (+ 1
           (ssg15-l-strspn
            memory
            (ssg15-shift string 1)
            accept))
        (ssg15-l-strspn memory string accept)))))))

;; For each source-prefix address, the matching accept-string address remains
;; an internal existential over the complete integer-pair address domain.

(defun-sk ssg15-accept-witness-p
    (memory source-candidate accept-start accept-end)
  (exists (accept-candidate)
    (and
     (ssg15-address-p accept-candidate)
     (equal
      (ssg15-character-memory memory source-candidate)
      (ssg15-character-memory memory accept-candidate))
     (ssg15-addr-le-p
      accept-start
      accept-candidate)
     (ssg15-addr-lt-p
      accept-candidate
      accept-end))))

(defun-sk ssg15-prefix-values-in-accept-p
    (memory source-start source-current accept-start accept-end)
  (forall (source-candidate)
    (implies
     (ssg15-address-p source-candidate)
     (implies
      (ssg15-addr-lt-p
       source-candidate
       source-current)
      (implies
       (ssg15-addr-le-p
        source-start
        source-candidate)
       (ssg15-accept-witness-p
        memory
        source-candidate
        accept-start
        accept-end))))))

(defun-sk
    ntp4vc-strspn-loop-inv-8-established-goal15-statement ()
  (forall
   (memory a1 a a3 a2)
   (implies
    (and
     (ssg15-address-p a1)
     (ssg15-address-p a)
     (ssg15-address-p a3)
     (ssg15-address-p a2)
     (ssg15-function-types-p)
     (ssg15-memory-extensionality-p)
     (ssg15-address-order-laws-p)
     (ssg15-to-uint64-laws-p)
     (ssg15-strlen-laws-p)
     (ssg15-strspn-laws-p))
    (let*
        ((x
          (ssg15-character-memory memory a1))
         (x1
          (ssg15-address-offset a1))
         (x2
          (ssg15-address-offset a))
         (x3
          (ssg15-l-strlen memory a))
         (accept-end
          (ssg15-shift
           a3
           (ssg15-l-strlen memory a3))))
      (implies
       (and
        (not (equal x 0))
        (equal
         (+ x1
            (ssg15-l-strspn memory a1 a3))
         (+ x2
            (ssg15-l-strspn memory a a3)))
        (<= x2 x1)
        (<=
         (ssg15-region
          (ssg15-address-base a))
         0)
        (<=
         (ssg15-region
          (ssg15-address-base a3))
         0)
        (<= x1 (+ x2 x3))
        (ssg15-linked-p)
        (ssg15-sconst-p memory)
        (ssg15-addr-lt-p a2 a3)
        (ssg15-addr-le-p a a1)
        (ssg15-addr-le-p a3 a2)
        (ssg15-is-sint8-p x)
        (ssg15-valid-string-p memory a)
        (ssg15-valid-string-p memory a1)
        (ssg15-valid-string-p memory a3)
        (ssg15-is-uint64-p (- x1 x2))
        (ssg15-addr-le-p
         a1
         (ssg15-shift a x3))
        (ssg15-prefix-values-in-accept-p
         memory a a1 a3 accept-end))
       (not
        (equal
         (ssg15-character-memory memory a2)
         x)))))))

(value-triple :itpeval-statement-checked)

:q
