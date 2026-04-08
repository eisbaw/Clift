struct node {
    int val;
    struct node *next;
};

int list_length(struct node *head) {
    int count = 0;
    while (head != 0) {
        count++;
        head = head->next;
    }
    return count;
}
