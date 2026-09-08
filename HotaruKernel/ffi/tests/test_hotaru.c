#include "hotaru.h"
#include <assert.h>
#include <pthread.h>
#include <stdio.h>
#include <string.h>

#define P "{\"fvar\":[\"p\",\"bool\"]}"
#define REFL "{\"infer\":{\"rule\":{\"refl\":{\"p\":" P "}}}}"
#define SYMM "{\"infer\":{\"rule\":{\"symm\":{\"th\":4}}}}"

static void rejected(const hotaru_state *s, const char *input, const char *error) {
    hotaru_state *next = NULL;
    char *response = NULL;
    assert(hotaru_apply(s, input, strlen(input), &next, &response) == HOTARU_REJECTED);
    if (!response || !strstr(response, error))
        fprintf(stderr, "Expected %s, got %s for %s\n", error,
                response ? response : "NULL", input);
    assert(next == NULL && response != NULL && strstr(response, error));
    hotaru_string_free(response);
}

static void *wrong_thread(void *arg) {
    hotaru_state *s = arg;
    char *response = NULL;
    assert(hotaru_init() == HOTARU_WRONG_THREAD);
    assert(hotaru_theorem(s, 0, &response) == HOTARU_WRONG_THREAD);
    assert(response == NULL);
    assert(hotaru_state_free(s) == HOTARU_WRONG_THREAD);
    return NULL;
}

int main(void) {
    assert(hotaru_abi_version() == 1);
    assert(hotaru_init() == HOTARU_OK);
    assert(hotaru_init() == HOTARU_OK);
    assert(hotaru_state_new(NULL) == HOTARU_INVALID_ARGUMENT);
    hotaru_state *base = NULL;
    assert(hotaru_state_new(&base) == HOTARU_OK);
    char *response = NULL;
    assert(hotaru_theorem(base, 0, &response) == HOTARU_OK);
    assert(strstr(response, "\"ok\":true"));
    hotaru_string_free(response);

    const char *commands = "[" REFL "," SYMM "]";
    hotaru_state *next = NULL;
    assert(hotaru_apply(base, commands, strlen(commands), &next, &response) == HOTARU_OK);
    assert(strstr(response, "\"theoremCount\":6"));
    hotaru_string_free(response);
    assert(hotaru_theorem(next, 5, &response) == HOTARU_OK);
    assert(strcmp(response, "{\"assumptions\":[],\"conclusion\":{\"equal\":[" P "," P "]},\"ok\":true}") == 0);
    hotaru_string_free(response);
    assert(hotaru_theorem(base, 4, &response) == HOTARU_REJECTED);
    hotaru_string_free(response);
    assert(hotaru_theorem(next, UINT64_MAX, &response) == HOTARU_REJECTED);
    hotaru_string_free(response);

    rejected(base, "[", "json");
    rejected(base, "[{}]", "command");
    rejected(base, "[" SYMM "]", "invalidTheoremReference");
    rejected(base, "[" REFL ",{\"infer\":{\"rule\":{\"symm\":{\"th\":99}}}}]",
             "invalidTheoremReference");
    rejected(base, "[{\"infer\":{\"rule\":{\"refl\":{\"p\":{\"bvar\":0}}}}}]", "unboundVariable");
    rejected(base, "[{\"infer\":{\"rule\":{\"assume\":{\"p\":{\"lam\":[\"bool\",{\"bvar\":0}]}}}}}]", "notBoolean");
    rejected(base, "[{\"infer\":{\"rule\":{\"assume\":{\"p\":{\"equal\":[" P "," P "]}}}}},"
                   "{\"infer\":{\"rule\":{\"abs\":{\"name\":\"p\",\"type\":\"bool\",\"th\":4}}}}]",
             "freeInAssumptions");
    rejected(base, "[{\"infer\":{\"rule\":{\"refl\":{\"p\":{\"app\":[" P "," P "]}}}}}]",
             "notFunction");
    rejected(base, "[{\"infer\":{\"rule\":{\"refl\":{\"p\":{\"const\":[{\"theory\":\"test\",\"name\":\"missing\"},[]]}}}}}]",
             "unknownConstant");
    rejected(base, "[{\"infer\":{\"rule\":{\"refl\":{\"p\":{\"fvar\":[\"x\",{\"op\":[{\"theory\":\"test\",\"name\":\"missing\"},[]]}]}}}}}]",
             "invalidType");
    rejected(base, "[{\"declareType\":{\"name\":{\"theory\":\"test\",\"name\":\"t\"},\"arity\":0}},"
                   "{\"declareType\":{\"name\":{\"theory\":\"test\",\"name\":\"t\"},\"arity\":0}}]",
             "duplicateType");
    rejected(base, "[{\"defineConstant\":{\"name\":{\"theory\":\"test\",\"name\":\"c\"},\"rhs\":" P "}}]",
             "freeVariablesInDefinition");
    rejected(base, "[{\"defineType\":{\"name\":{\"theory\":\"test\",\"name\":\"t\"},\"parameters\":[],\"predicate\":{\"lam\":[\"bool\",{\"bvar\":0}]},\"proof\":null}}]",
             "missingNonemptyProof");
    hotaru_state *bad = NULL;
    assert(hotaru_apply(base, "\xff", 1, &bad, &response) == HOTARU_INVALID_ARGUMENT);
    assert(bad == NULL && response == NULL);
    assert(hotaru_apply(NULL, "[]", 2, &bad, &response) == HOTARU_INVALID_ARGUMENT);

    const char *definition = "[{\"defineConstant\":{\"name\":{\"theory\":\"test\",\"name\":\"id\"},"
                             "\"rhs\":{\"lam\":[\"bool\",{\"bvar\":0}]}}}]";
    hotaru_state *extended = NULL;
    assert(hotaru_apply(base, definition, strlen(definition), &extended, &response) == HOTARU_OK);
    hotaru_string_free(response);
    assert(hotaru_theorem(extended, 4, &response) == HOTARU_OK);
    assert(strstr(response, "\"const\""));
    hotaru_string_free(response);
    assert(hotaru_state_free(extended) == HOTARU_OK);

    pthread_t thread;
    assert(pthread_create(&thread, NULL, wrong_thread, base) == 0);
    assert(pthread_join(thread, NULL) == 0);
    assert(hotaru_state_free(base) == HOTARU_OK);
    /* A descendant owns its data independently of its ancestor's C handle. */
    assert(hotaru_theorem(next, 4, &response) == HOTARU_OK);
    hotaru_string_free(response);
    for (int i = 0; i < 100; ++i) {
        hotaru_state *copy = NULL;
        assert(hotaru_apply(next, "[]", 2, &copy, &response) == HOTARU_OK);
        hotaru_string_free(response);
        assert(hotaru_state_free(copy) == HOTARU_OK);
    }
    assert(hotaru_state_free(next) == HOTARU_OK);
    assert(hotaru_state_free(NULL) == HOTARU_OK);
    hotaru_string_free(NULL);
    puts("C ABI tests passed");
    return 0;
}
