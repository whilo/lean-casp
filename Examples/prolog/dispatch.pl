consumer(ui).
eligible(ui).
sameDrain(ui,store).
dependsOn(ui,store).
forward(X) :- consumer(X), eligible(X), not reverse(X).
reverse(X) :- consumer(X), eligible(X), not forward(X).
