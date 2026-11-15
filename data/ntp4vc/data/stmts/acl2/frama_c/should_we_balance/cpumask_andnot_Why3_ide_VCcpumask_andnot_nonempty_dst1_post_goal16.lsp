;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/should_we_balance/cpumask_andnot_Why3_ide_VCcpumask_andnot_nonempty_dst1_post_goal16:
;; the cpumask-andnot nonempty-destination postcondition, relating the source
;; mask entries to the havoced destination entry under the stated memory,
;; framing, separation, and quantified loop-invariant hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun cpn16-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun cpn16-address-base (address)
  (car address))

(defun cpn16-address-offset (address)
  (cdr address))

(defun cpn16-shift (address amount)
  (cons
   (cpn16-address-base address)
   (+ (cpn16-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_3, integer memories t_1 and t_2, allocation map t, and the
;; fixed region function, CPU-mask address function, linked predicate, and
;; l_size constant.

(defstub cpn16-t3 (address) t)
(defstub cpn16-t1 (address) t)
(defstub cpn16-t2 (address) t)
(defstub cpn16-allocation (index) t)
(defstub cpn16-region (base) t)
(defstub cpn16-l-cpu-smt-mask (index) t)
(defstub cpn16-linked-op () t)
(defstub cpn16-l-size () t)
(defstub cpn16-l-idle-cpu (index) t)
(defstub cpn16-mask-memory-apply (memory-symbol address) t)
(defstub cpn16-mask-pointer-apply (pointer-symbol address) t)

(defun-sk cpn16-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (cpn16-address-p address)
      (and
       (cpn16-address-p (cpn16-t3 address))
       (integerp (cpn16-t1 address))
       (integerp (cpn16-t2 address))))
     (implies
      (integerp index)
      (and
       (integerp (cpn16-allocation index))
       (cpn16-address-p (cpn16-l-cpu-smt-mask index))))
     (implies
      (integerp base)
      (integerp (cpn16-region base))))))

(defun cpn16-linked-p ()
  (if (cpn16-linked-op) t nil))

;; Cint.to_uint32 is the canonical residue in [0, 2^32), the mathematical
;; unsigned 32-bit conversion on every source integer.

(defun cpn16-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

(defun cpn16-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))
(defun cpn16-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

;; Preserve A_schedule_cpumask over arbitrary reified integer and pointer
;; memories.  The distinguished zero-memory symbol witnesses the source's
;; constant-zero memory; without it, the reification would silently weaken the
;; unrestricted memory quantifiers.

(defun-sk cpn16-scheduler-schema-types-p ()
  (forall (memory-symbol pointer-symbol address index)
    (and
     (implies
      (cpn16-address-p address)
      (and
       (integerp
        (cpn16-mask-memory-apply
         memory-symbol address))
       (cpn16-address-p
        (cpn16-mask-pointer-apply
         pointer-symbol address))))
     (implies
      (integerp index)
      (and
       (cpn16-is-uint8-p
        (cpn16-l-idle-cpu index))
       (cpn16-address-p
        (cpn16-l-cpu-smt-mask index)))))))

(defun-sk cpn16-zero-mask-memory-instance-p ()
  (forall (address)
    (implies
     (cpn16-address-p address)
     (equal
      (cpn16-mask-memory-apply
       'cpn16-zero-memory address)
      0))))

(defun-sk cpn16-q-mask-refl-p ()
  (forall (index memory-symbol pointer-symbol)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (cpn16-l-size)))
     (not
      (equal
       (cpn16-mask-memory-apply
        memory-symbol
        (cpn16-shift
         (cpn16-mask-pointer-apply
          pointer-symbol
          (cpn16-shift
           (cpn16-l-cpu-smt-mask index)
           0))
         index))
       0)))))

(defun-sk cpn16-q-mask-symm-p ()
  (forall (memory-symbol pointer-symbol j i)
    (implies
     (and
      (integerp i)
      (integerp j)
      (not
       (equal
        (cpn16-mask-memory-apply
         memory-symbol
         (cpn16-shift
          (cpn16-mask-pointer-apply
           pointer-symbol
           (cpn16-shift
            (cpn16-l-cpu-smt-mask j)
            0))
          i))
        0))
      (<= 0 i)
      (< i (cpn16-l-size))
      (<= 0 j)
      (< j (cpn16-l-size)))
     (not
      (equal
       (cpn16-mask-memory-apply
        memory-symbol
        (cpn16-shift
         (cpn16-mask-pointer-apply
          pointer-symbol
          (cpn16-shift
           (cpn16-l-cpu-smt-mask i)
           0))
         j))
       0)))))

(defun-sk cpn16-q-mask-trans-p ()
  (forall (pointer-symbol i memory-symbol j k)
    (implies
     (and
      (integerp i)
      (integerp j)
      (integerp k)
      (not
       (equal
        (cpn16-mask-memory-apply
         memory-symbol
         (cpn16-shift
          (cpn16-mask-pointer-apply
           pointer-symbol
           (cpn16-shift
            (cpn16-l-cpu-smt-mask i)
            0))
          j))
        0))
      (not
       (equal
        (cpn16-mask-memory-apply
         memory-symbol
         (cpn16-shift
          (cpn16-mask-pointer-apply
           pointer-symbol
           (cpn16-shift
            (cpn16-l-cpu-smt-mask j)
            0))
          k))
        0))
      (<= 0 i)
      (< i (cpn16-l-size))
      (<= 0 j)
      (< j (cpn16-l-size))
      (<= 0 k)
      (< k (cpn16-l-size)))
     (not
      (equal
       (cpn16-mask-memory-apply
        memory-symbol
        (cpn16-shift
         (cpn16-mask-pointer-apply
          pointer-symbol
          (cpn16-shift
           (cpn16-l-cpu-smt-mask i)
           0))
         k))
       0)))))


;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun cpn16-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (cpn16-address-base address))
    (<= 0 (cpn16-address-offset address))
    (<=
     (+ (cpn16-address-offset address) length)
     (cpn16-allocation (cpn16-address-base address))))))

(defun cpn16-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (cpn16-address-base address)))
    (<= 0 (cpn16-address-offset address))
    (<=
     (+ (cpn16-address-offset address) length)
     (cpn16-allocation (cpn16-address-base address))))))

(defun cpn16-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (cpn16-address-base left)
     (cpn16-address-base right)))
   (<=
    (+ (cpn16-address-offset right) right-length)
    (cpn16-address-offset left))
   (<=
    (+ (cpn16-address-offset left) left-length)
    (cpn16-address-offset right))))

;; Exact unfolding of Memory.framed for the arbitrary pointer memory t_3.

(defun-sk cpn16-framed-p ()
  (forall (address)
    (implies
     (cpn16-address-p address)
     (<=
      (cpn16-region
       (cpn16-address-base (cpn16-t3 address)))
      0))))

;; This is the exact havoc_access value for
;; havoc t_1 t_2 protected-start protected-length at query.

(defun cpn16-havoc-value
    (protected-start protected-length query)
  (if
      (cpn16-separated-p
       query 1 protected-start protected-length)
      (cpn16-t2 query)
    (cpn16-t1 query)))

;; Preserve the source universal separation condition for every integer i_2
;; in [0, l_size).

(defun-sk cpn16-mask-separated-p (a8)
  (forall (i2)
    (implies
     (integerp i2)
     (implies
      (<= 0 i2)
      (implies
       (< i2 (cpn16-l-size))
       (cpn16-separated-p
        a8
        (cpn16-l-size)
        (cpn16-shift
         (cpn16-t3
          (cpn16-shift (cpn16-l-cpu-smt-mask i2) 0))
         0)
        (cpn16-l-size)))))))

;; Preserve the source universal agreement between the havoced memory and t_2
;; from the current index through the end of the mask.

(defun-sk cpn16-tail-havoc-agreement-p (a7 a8 i)
  (forall (i2)
    (implies
     (integerp i2)
     (implies
      (<= i i2)
      (implies
       (< i2 (cpn16-l-size))
       (let ((a10 (cpn16-shift a7 i2)))
         (iff
          (not
           (equal
            (cpn16-havoc-value
             a8
             (cpn16-l-size)
             a10)
            0))
          (not (equal (cpn16-t2 a10) 0)))))))))

;; Preserve the source universal loop invariant over every earlier integer
;; index i_2.

(defun-sk cpn16-prefix-invariant-p (a3 a5 a7 a8 i)
  (forall (i2)
    (implies
     (integerp i2)
     (implies
      (<= 0 i2)
      (implies
       (< i2 i)
       (iff
        (and
         (equal (cpn16-t2 (cpn16-shift a3 i2)) 0)
         (not
          (equal
           (cpn16-t2 (cpn16-shift a5 i2))
           0)))
        (not
         (equal
          (cpn16-havoc-value
           a8
           (cpn16-l-size)
           (cpn16-shift a7 i2))
          0))))))))

(defun-sk
    ntp4vc-cpumask-andnot-nonempty-dst1-post-goal16-statement ()
  (forall
   (a a1 a2 i i1)
   (implies
    (and
     (cpn16-function-types-p)
     (cpn16-scheduler-schema-types-p)
     (cpn16-zero-mask-memory-instance-p)
     (cpn16-q-mask-refl-p)
     (cpn16-q-mask-symm-p)
     (cpn16-q-mask-trans-p)
     (integerp (cpn16-l-size))
     (< 0 (cpn16-l-size))
     (<= (cpn16-l-size) 2147483647)
     (cpn16-address-p a)
     (cpn16-address-p a1)
     (cpn16-address-p a2)
     (integerp i)
     (integerp i1))
    (let*
        ((a3 (cpn16-t3 (cpn16-shift a 0)))
         (a4 (cpn16-shift a3 0))
         (a5 (cpn16-t3 (cpn16-shift a1 0)))
         (a6 (cpn16-shift a5 0))
         (a7 (cpn16-t3 (cpn16-shift a2 0)))
         (a8 (cpn16-shift a7 0)))
      (implies
       (and
        (not (equal (cons 0 0) a2))
        (equal
         (cpn16-to-uint32 i)
         (cpn16-l-size))
        (<= 0 i)
        (<= 0 i1)
        (< i1 (cpn16-l-size))
        (<= i (cpn16-l-size))
        (<= (cpn16-region (cpn16-address-base a)) 0)
        (<= (cpn16-region (cpn16-address-base a1)) 0)
        (<= (cpn16-region (cpn16-address-base a2)) 0)
        (cpn16-framed-p)
        (cpn16-linked-p)
        (cpn16-is-sint32-p i)
        (cpn16-valid-rd-p a 1)
        (cpn16-valid-rd-p a1 1)
        (cpn16-valid-rd-p a2 1)
        (cpn16-valid-rd-p a4 (cpn16-l-size))
        (cpn16-valid-rd-p a6 (cpn16-l-size))
        (cpn16-valid-rw-p a8 (cpn16-l-size))
        (implies
         (not (equal a2 a))
         (cpn16-separated-p
          a8 (cpn16-l-size) a4 (cpn16-l-size)))
        (implies
         (not (equal a2 a1))
         (cpn16-separated-p
          a8 (cpn16-l-size) a6 (cpn16-l-size)))
        (cpn16-mask-separated-p a8)
        (cpn16-tail-havoc-agreement-p a7 a8 i)
        (cpn16-prefix-invariant-p a3 a5 a7 a8 i))
       (iff
        (and
         (equal (cpn16-t2 (cpn16-shift a3 i1)) 0)
         (not
          (equal
           (cpn16-t2 (cpn16-shift a5 i1))
           0)))
        (not
         (equal
          (cpn16-havoc-value
           a8
           (cpn16-l-size)
           (cpn16-shift a7 i1))
          0))))))))

(value-triple :itpeval-statement-checked)

:q
