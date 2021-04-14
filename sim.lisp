; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s

(defmacro let-match* (binds body)
  (case-match binds
    ('() body)
    (((pat val) . rst)
     `(let ((greatbadness ,val))
	(case-match greatbadness
	  (,pat (let-match* ,rst ,body)))))))

;; ---- Definitions ----

(defdata data (listof atom))

(defdata sender-state `(sendstate ,data ,nat))

(defdata receiver-state `(recvstate ,data ,nat))

(defdata ack nat)

(defdata packet `(packet ,atom ,ack))

(defdata event-deck (listof nil))
;; Sim-state -- (sender-state receiver-state steps)
(defdata sim-state `(sim-state ,sender-state ,receiver-state ,event-deck))

;; LHS contains the sender's updated state, RHS is the packet to be sent
(defdata sender-out `(sender-out ,sender-state ,packet))

;; LHS contains the sender's updated state, RHS is the packet to be sent
(defdata receiver-out `(receiver-out ,receiver-state ,ack))

(defdata result (oneof data 'error))

;; ---- Functions ----

(definec seq-num-okp (sender-state :sender-state) :bool
  (let-match* ((('sendstate data seq-num) sender-state))
    (> (len data) seq-num)))

(set-ignore-ok t)
(definec simulator-state-check (sim :sim-state) :bool
  (let-match* ((('sim-state sender-state & steps) sim))
    (and (consp steps)
	 (seq-num-okp sender-state))))

(definec simulator-step (sim :sim-state) :sim-state
  :ic (simulator-state-check sim)
  (let-match* ((('sim-state ('sendstate sdata sseq) ('recvstate rdata rseq) steps) sim))
    `(sim-state (sendstate ,sdata ,(1+ sseq))
		(recvstate ,(app rdata (list (nth sseq sdata))) ,rseq)
		,(cdr steps))))

(check= (simulator-step '(sim-state (sendstate (1 2) 0) (recvstate nil 0) (nil nil nil)))
	'(sim-state (sendstate (1 2) 1) (recvstate (1) 0) (nil nil)))

(check= (simulator-step '(sim-state (sendstate (1) 0) (recvstate (4 5 6) 0) (nil)))
	'(sim-state (sendstate (1) 1) (recvstate (4 5 6 1) 0) ()))

(definec simulator-measure (sim :sim-state) :nat
  "Retreives the length of the event-deck."
  (len (cadddr sim)))

(definec simulator-state-check2 (sim :sim-state) :bool
  (let-match* ((('sim-state ('sendstate data seqnum) & &) sim))
    (>= (len data) seqnum)))

(definec simulator (sim :sim-state) :sim-state
  (define (xargs :measure (simulator-measure sim)
		 :termination-method :measure))
  :ic (simulator-state-check2 sim)
  (let-match* ((('sim-state ('sendstate ss seqnum) ('recvstate rs &) steps) sim))
    (cond
     ((or (equal seqnum (len ss)) (lendp steps)) sim)
     (T (simulator (simulator-step sim))))))

(check= (simulator '(sim-state (sendstate (1 2 3) 0) (recvstate (4 5 6) 0) (nil nil nil)))
	'(4 5 6 1 2 3))

(definec simulator* (data :data steps :event-deck) :data
  :function-contract-strictp nil
  :ic (>= (len data) (len steps))
  (let-match* ((('sim-state & ('recvstate rs &) steps)
		(simulator `(sim-state (sendstate ,data 0) (recvstate nil 0) ,steps))))
    rs))

(check= (simulator* '(4 5 6) '(nil nil nil))
	'(4 5 6))

;; ---- Proofs ----

;; Checks if x is a prefix of y
(definec prefixp (x :tl y :tl) :bool
  (cond
   ((lendp x) T)
   ((lendp y) (lendp x))
   (T (and (equal (car x) (car y))
	   (prefixp (cdr x) (cdr y))))))

;; First confirm test? works
(test? (implies (and (datap d)
		     (event-deckp n)
		     (>= (len d) (len n)))
		(prefixp (simulator* d n) d)))

(defthm prefix-nth
  (implies (and
	    (tlp x)
	    (tlp y)
	    (prefixp x y)
	    (< (len x) (len y)))
	   (prefixp (app x (list (nth (len x) y))) y)))

(definec rs-prefix-of-ssp (sim :sim-state) :bool
  (let-match* ((('sim-state ('sendstate ss &) ('recvstate rs &) steps) sim))
    (prefixp rs ss)))

;; (in-theory (disable (:definition rs-prefix-of-ssp)))

(definec seqnum-consistent (sim :sim-state) :bool
  (let-match* ((('sim-state ('sendstate & sseq) ('recvstate rs rseq) steps) sim))
    (and (== rseq sseq)
	 (== (len rs) rseq))))

(defthm foo
  (implies (and (sim-statep sim)
		(simulator-state-check sim)
		(rs-prefix-of-ssp sim)
		(seqnum-consistent sim))
	   (let-match* ((('sim-state ('sendstate sdata sseq) ('recvstate rdata rseq) steps) sim))
	     (prefixp (app rdata (list (nth sseq sdata))) sdata)))
  :hints (("Goal" :do-not-induct t)
	  ("Goal'4'" :use ((:instance prefix-nth (x rdata) (y sdata))))))

(skip-proofs
 (defthm simulator-step-prefix-property
   (implies (and (sim-statep sim)
		 (simulator-state-check2 sim)
		 (rs-prefix-of-ssp sim)
		 (seqnum-consistent sim))
	    (rs-prefix-of-ssp (simulator-step sim)))
   :hints (("Goal" :do-not-induct t
	    :do-not generalize)
	   ;; ("Goal'''" :use (:instance prefix-nth
	   ;; 			     (x (CADR (CADDR SIM)))
	   ;; 			     (y (CADR (CADR sim)))))
	   )))
(in-theory (disable simulator-step-definition-rule))
(defthm simulator-prefix-property
  (implies (and (sim-statep sim)
		(simulator-state-check2 sim)
		(rs-prefix-of-ssp sim)
		(seqnum-consistent sim))
	   (rs-prefix-of-ssp (simulator sim)))
  :hints (("Goal" :induct (simulator sim))))

(defthm data-never-out-of-order
  (implies (and (datap d)
		(event-deckp n)
		(>= (len d) (len n)))
	   (prefixp (simulator* d n) d)))

 
