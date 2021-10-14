//////////////////////////////////////////////////////////////////////////////////////
//
//  The MIT License (MIT)
//
//  Copyright (c) 2015-present, Dom Chen.
//  All rights reserved.
//
//  Permission is hereby granted, free of charge, to any person obtaining a copy of
//  this software and associated documentation files (the "Software"), to deal in the
//  Software without restriction, including without limitation the rights to use, copy,
//  modify, merge, publish, distribute, sublicense, and/or sell copies of the Software,
//  and to permit persons to whom the Software is furnished to do so, subject to the
//  following conditions:
//
//      The above copyright notice and this permission notice shall be included in all
//      copies or substantial portions of the Software.
//
//  THE SOFTWARE IS PROVIDED *AS IS*, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED,
//  INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
//  PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
//  HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
//  OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
//  SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//
//////////////////////////////////////////////////////////////////////////////////////

// @see https://github.com/domchen/typescript-plus/blob/master/src/compiler/sorting.ts

namespace ts {

    let checker: TypeChecker | null;
    let sourceFiles: SourceFile[];
    let rootFileNames: string[];
    let dependencyMap: { [path: string]: string[] };
    let pathWeightMap: { [path: string]: number };
    let visitedBlocks: Block[];
    const calledMethods: MethodDeclaration[] = [];

    export interface SortingResult {
        sortedFileNames: string[],
        circularReferences: string[]
    }

    export function reorderSourceFiles(program: Program): SortingResult {
        sourceFiles = program.getSourceFiles() as any;
        rootFileNames = program.getRootFileNames() as any;
        checker = program.getTypeChecker();
        visitedBlocks = [];
        buildDependencyMap();
        const result = sortOnDependency();
        sourceFiles = [];
        rootFileNames = [];
        visitedBlocks = [];
        return result;
    }


    function addDependency(file: string, dependent: string): void {
        if (file === dependent) {
            return;
        }
        let list = dependencyMap[file];
        if (!list) {
            list = dependencyMap[file] = [];
        }
        if (list.indexOf(dependent) === -1) {
            list.push(dependent);
        }
    }

    function buildDependencyMap(): void {
        dependencyMap = {};
        // eslint-disable-next-line @typescript-eslint/prefer-for-of
        for (let i = 0; i < sourceFiles.length; i++) {
            const sourceFile = sourceFiles[i];
            if (sourceFile.isDeclarationFile) {
                continue;
            }
            visitFile(sourceFile);
        }
    }

    function visitFile(sourceFile: SourceFile): void {
        const statements = sourceFile.statements;
        const length = statements.length;
        for (let i = 0; i < length; i++) {
            const statement = statements[i];
            if (hasAmbientModifier(statement)) { // has the 'declare' keyword
                continue;
            }
            visitStatement(statements[i]);
        }
    }

    function visitStatement(statement?: Statement): void {
        if (!statement) {
            return;
        }
        switch (statement.kind) {
            case SyntaxKind.ExpressionStatement:
                const expression = statement as ExpressionStatement;
                visitExpression(expression.expression);
                break;
            case SyntaxKind.ClassDeclaration:
                checkInheriting(statement as ClassDeclaration);
                visitStaticMember(statement as ClassDeclaration);
                if (statement.transformFlags & TransformFlags.ContainsTypeScriptClassSyntax) {
                    visitClassDecorators(statement as ClassDeclaration);
                }
                break;
            case SyntaxKind.VariableStatement:
                visitVariableList((statement as VariableStatement).declarationList);
                break;
            case SyntaxKind.ImportEqualsDeclaration:
                const importDeclaration = statement as ImportEqualsDeclaration;
                checkDependencyAtLocation(importDeclaration.moduleReference);
                break;
            case SyntaxKind.ModuleDeclaration:
                visitModule(statement as ModuleDeclaration);
                break;
            case SyntaxKind.Block:
                visitBlock(statement as Block);
                break;
            case SyntaxKind.IfStatement:
                const ifStatement = statement as IfStatement;
                visitExpression(ifStatement.expression);
                visitStatement(ifStatement.thenStatement);
                visitStatement(ifStatement.elseStatement);
                break;
            case SyntaxKind.DoStatement:
            case SyntaxKind.WhileStatement:
            case SyntaxKind.WithStatement:
                const doStatement = statement as DoStatement;
                visitExpression(doStatement.expression);
                visitStatement(doStatement.statement);
                break;
            case SyntaxKind.ForStatement:
                const forStatement = statement as ForStatement;
                visitExpression(forStatement.condition);
                visitExpression(forStatement.incrementor);
                if (forStatement.initializer) {
                    if (forStatement.initializer.kind === SyntaxKind.VariableDeclarationList) {
                        visitVariableList(forStatement.initializer as VariableDeclarationList);
                    }
                    else {
                        visitExpression(forStatement.initializer);
                    }
                }
                break;
            case SyntaxKind.ForInStatement:
            case SyntaxKind.ForOfStatement:
                const forInStatement = statement as ForInStatement;
                visitExpression(forInStatement.expression);
                if (forInStatement.initializer) {
                    if (forInStatement.initializer.kind === SyntaxKind.VariableDeclarationList) {
                        visitVariableList(forInStatement.initializer as VariableDeclarationList);
                    }
                    else {
                        visitExpression(forInStatement.initializer);
                    }
                }
                break;
            case SyntaxKind.ReturnStatement:
                visitExpression((statement as ReturnStatement).expression);
                break;
            case SyntaxKind.SwitchStatement:
                const switchStatment = statement as SwitchStatement;
                visitExpression(switchStatment.expression);
                switchStatment.caseBlock.clauses.forEach(element => {
                    if (element.kind === SyntaxKind.CaseClause) {
                        visitExpression((element).expression);
                    }
                    (element as DefaultClause).statements.forEach(element => {
                        visitStatement(element);
                    });
                });
                break;
            case SyntaxKind.LabeledStatement:
                visitStatement((statement as LabeledStatement).statement);
                break;
            case SyntaxKind.ThrowStatement:
                visitExpression((statement as ThrowStatement).expression);
                break;
            case SyntaxKind.TryStatement:
                const tryStatement = statement as TryStatement;
                visitBlock(tryStatement.tryBlock);
                visitBlock(tryStatement.finallyBlock);
                if (tryStatement.catchClause) {
                    visitBlock(tryStatement.catchClause.block);
                }
                break;
        }
    }

    function visitModule(node: ModuleDeclaration): void {
        if (node.body!.kind === SyntaxKind.ModuleDeclaration) {
            visitModule(node.body as ModuleDeclaration);
            return;
        }
        if (node.body!.kind === SyntaxKind.ModuleBlock) {
            for (const statement of (node.body as ModuleBlock).statements) {
                if (hasAmbientModifier(statement)) { // has the 'declare' keyword
                    continue;
                }
                visitStatement(statement);
            }
        }

    }

    function checkDependencyAtLocation(node: Node): void {
        const symbol = checker!.getSymbolAtLocation(node);
        if (!symbol || !symbol.declarations) {
            return;
        }
        const sourceFile = getSourceFileOfNode(symbol.declarations[0]);
        if (!sourceFile || sourceFile.isDeclarationFile) {
            return;
        }
        addDependency(getSourceFileOfNode(node).fileName, sourceFile.fileName);
    }

    function checkInheriting(node: ClassDeclaration): void {
        if (!node.heritageClauses) {
            return;
        }
        let heritageClause: HeritageClause | undefined;
        for (const clause of node.heritageClauses) {
            if (clause.token === SyntaxKind.ExtendsKeyword) {
                heritageClause = clause;
                break;
            }
        }
        if (!heritageClause) {
            return;
        }
        const superClasses = heritageClause.types;
        if (!superClasses) {
            return;
        }
        superClasses.forEach(superClass => {
            checkDependencyAtLocation(superClass.expression);
        });
    }

    function visitStaticMember(node: ClassDeclaration): void {
        const members = node.members;
        if (!members) {
            return;
        }
        for (const member of members) {
            if (!hasStaticModifier(member)) {
                continue;
            }
            if (member.kind === SyntaxKind.PropertyDeclaration) {
                const property = member as PropertyDeclaration;
                visitExpression(property.initializer);
            }
        }
    }

    function visitClassDecorators(node: ClassDeclaration): void {
        if (node.decorators) {
            visitDecorators(node.decorators);
        }
        const members = node.members;
        if (!members) {
            return;
        }
        for (const member of members) {
            let decorators: NodeArray<Decorator> | undefined;
            let functionLikeMember: FunctionLikeDeclaration | undefined;
            if (member.kind === SyntaxKind.GetAccessor || member.kind === SyntaxKind.SetAccessor) {
                const accessors = getAllAccessorDeclarations(node.members, member as AccessorDeclaration);
                if (member !== accessors.firstAccessor) {
                    continue;
                }
                decorators = accessors.firstAccessor.decorators;
                if (!decorators && accessors.secondAccessor) {
                    decorators = accessors.secondAccessor.decorators;
                }
                functionLikeMember = accessors.setAccessor;
            }
            else {
                decorators = member.decorators;
                if (member.kind === SyntaxKind.MethodDeclaration) {
                    functionLikeMember = member as MethodDeclaration;
                }
            }
            if (decorators) {
                visitDecorators(decorators);
            }

            if (functionLikeMember) {
                for (const parameter of functionLikeMember.parameters) {
                    if (parameter.decorators) {
                        visitDecorators(parameter.decorators);
                    }
                }
            }
        }
    }

    function visitDecorators(decorators: NodeArray<Decorator>): void {
        for (const decorator of decorators) {
            visitCallExpression(decorator.expression);
        }
    }

    function visitExpression(expression?: Expression): void {
        if (!expression) {
            return;
        }
        switch (expression.kind) {
            case SyntaxKind.NewExpression:
            case SyntaxKind.CallExpression:
                visitCallArguments(expression as CallExpression);
                visitCallExpression((expression as CallExpression).expression);
                break;
            case SyntaxKind.Identifier:
                checkDependencyAtLocation(expression);
                break;
            case SyntaxKind.PropertyAccessExpression:
                checkDependencyAtLocation(expression);
                break;
            case SyntaxKind.ElementAccessExpression:
                visitExpression((expression as PropertyAccessExpression).expression);
                break;
            case SyntaxKind.ObjectLiteralExpression:
                visitObjectLiteralExpression(expression as ObjectLiteralExpression);
                break;
            case SyntaxKind.ArrayLiteralExpression:
                const arrayLiteral = expression as ArrayLiteralExpression;
                arrayLiteral.elements.forEach(visitExpression);
                break;
            case SyntaxKind.TemplateExpression:
                const template = expression as TemplateExpression;
                template.templateSpans.forEach(span => {
                    visitExpression(span.expression);
                });
                break;
            case SyntaxKind.ParenthesizedExpression:
                const parenthesized = expression as ParenthesizedExpression;
                visitExpression(parenthesized.expression);
                break;
            case SyntaxKind.BinaryExpression:
                visitBinaryExpression(expression as BinaryExpression);
                break;
            case SyntaxKind.PostfixUnaryExpression:
            case SyntaxKind.PrefixUnaryExpression:
                visitExpression((expression as PrefixUnaryExpression).operand);
                break;
            case SyntaxKind.DeleteExpression:
                visitExpression((expression as DeleteExpression).expression);
                break;
            case SyntaxKind.TaggedTemplateExpression:
                visitExpression((expression as TaggedTemplateExpression).tag);
                visitExpression((expression as TaggedTemplateExpression).template);
                break;
            case SyntaxKind.ConditionalExpression:
                visitExpression((expression as ConditionalExpression).condition);
                visitExpression((expression as ConditionalExpression).whenTrue);
                visitExpression((expression as ConditionalExpression).whenFalse);
                break;

            case SyntaxKind.SpreadElement:
                visitExpression((expression as SpreadElement).expression);
                break;
            case SyntaxKind.VoidExpression:
                visitExpression((expression as VoidExpression).expression);
                break;
            case SyntaxKind.YieldExpression:
                visitExpression((expression as YieldExpression).expression);
                break;
            case SyntaxKind.AwaitExpression:
                visitExpression((expression as AwaitExpression).expression);
                break;
            case SyntaxKind.TypeOfExpression:
                visitExpression((expression as TypeOfExpression).expression);
                break;
            case SyntaxKind.NonNullExpression:
                visitExpression((expression as NonNullExpression).expression);
                break;
            case SyntaxKind.TypeAssertionExpression:
                visitExpression((expression as TypeAssertion).expression);
                break;
        }

        // FunctionExpression
        // ArrowFunction
        // ClassExpression
        // OmittedExpression
        // ExpressionWithTypeArguments
        // AsExpression
    }

    function visitBinaryExpression(binary: BinaryExpression): void {
        const left = binary.left;
        const right = binary.right;
        visitExpression(left);
        visitExpression(right);
        if (binary.operatorToken.kind === SyntaxKind.EqualsToken &&
            (left.kind === SyntaxKind.Identifier || left.kind === SyntaxKind.PropertyAccessExpression) &&
            (right.kind === SyntaxKind.Identifier || right.kind === SyntaxKind.PropertyAccessExpression)) {
            const symbol = checker!.getSymbolAtLocation(left);
            if (!symbol || !symbol.declarations) {
                return;
            }
            for (const declaration of symbol.declarations) {
                if (declaration.kind === SyntaxKind.VariableDeclaration || declaration.kind === SyntaxKind.PropertyDeclaration) {
                    const variable = declaration as VariableDeclaration;
                    if (variable.initializer) {
                        continue;
                    }
                }
            }
        }
    }

    function visitObjectLiteralExpression(objectLiteral: ObjectLiteralExpression): void {
        objectLiteral.properties.forEach(element => {
            switch (element.kind) {
                case SyntaxKind.PropertyAssignment:
                    visitExpression((element).initializer);
                    break;
                case SyntaxKind.ShorthandPropertyAssignment:
                    visitExpression((element).objectAssignmentInitializer);
                    break;
                case SyntaxKind.SpreadAssignment:
                    visitExpression((element).expression);
                    break;
            }
        });
    }

    function visitCallArguments(callExpression: CallExpression): void {
        if (callExpression.arguments) {
            callExpression.arguments.forEach(argument => {
                visitExpression(argument);
            });
        }
    }

    function visitCallExpression(expression: Expression): void {
        expression = escapeParenthesized(expression);
        visitExpression(expression);
        switch (expression.kind) {
            case SyntaxKind.FunctionExpression:
                const functionExpression = expression as FunctionExpression;
                visitBlock(functionExpression.body);
                break;
            case SyntaxKind.PropertyAccessExpression:
            case SyntaxKind.Identifier:
                const callerFileName = getSourceFileOfNode(expression).fileName;
                checkCallTarget(callerFileName, expression);
                break;
            case SyntaxKind.CallExpression:
                visitReturnedFunction((expression as CallExpression).expression);
                break;
        }
    }

    function visitReturnedFunction(expression: Expression): Expression[] {
        expression = escapeParenthesized(expression);
        let returnExpressions: Expression[] = [];
        if (expression.kind === SyntaxKind.CallExpression) {
            const expressions = visitReturnedFunction((expression as CallExpression).expression);
            for (const returnExpression of expressions) {
                const returns = visitReturnedFunction(returnExpression);
                returnExpressions = returnExpressions.concat(returns);
            }
            return returnExpressions;
        }

        const functionBlocks: Block[] = [];
        switch (expression.kind) {
            case SyntaxKind.FunctionExpression:
                functionBlocks.push((expression as FunctionExpression).body);
                break;
            case SyntaxKind.PropertyAccessExpression:
            case SyntaxKind.Identifier:
                const callerFileName = getSourceFileOfNode(expression).fileName;
                const declarations: Declaration[] = [];
                getForwardDeclarations(expression, declarations, callerFileName);
                for (const declaration of declarations) {
                    const sourceFile = getSourceFileOfNode(declaration);
                    if (!sourceFile || sourceFile.isDeclarationFile) {
                        continue;
                    }
                    if (declaration.kind === SyntaxKind.FunctionDeclaration ||
                        declaration.kind === SyntaxKind.MethodDeclaration) {
                        functionBlocks.push((declaration as FunctionDeclaration).body!);
                    }
                }
                break;
        }

        for (const block of functionBlocks) {
            for (const statement of block.statements) {
                if (statement.kind === SyntaxKind.ReturnStatement) {
                    const returnExpression = (statement as ReturnStatement).expression;
                    returnExpressions.push(returnExpression!);
                    visitCallExpression(returnExpression!);
                }
            }
        }
        return returnExpressions;
    }

    function escapeParenthesized(expression: Expression): Expression {
        if (expression.kind === SyntaxKind.ParenthesizedExpression) {
            return escapeParenthesized((expression as ParenthesizedExpression).expression);
        }
        return expression;
    }

    function checkCallTarget(callerFileName: string, target: Node): void {
        const declarations: Declaration[] = [];
        getForwardDeclarations(target, declarations, callerFileName);
        for (const declaration of declarations) {
            const sourceFile = getSourceFileOfNode(declaration);
            if (!sourceFile || sourceFile.isDeclarationFile) {
                continue;
            }
            addDependency(callerFileName, sourceFile.fileName);
            if (declaration.kind === SyntaxKind.FunctionDeclaration) {
                visitBlock((declaration as FunctionDeclaration).body);
            }
            else if (declaration.kind === SyntaxKind.MethodDeclaration) {
                visitBlock((declaration as MethodDeclaration).body);
                calledMethods.push(declaration as MethodDeclaration);
            }
            else if (declaration.kind === SyntaxKind.ClassDeclaration) {
                checkClassInstantiation(declaration as ClassDeclaration);
            }
        }
    }

    function getForwardDeclarations(reference: Node, declarations: Declaration[], callerFileName: string): void {
        const symbol = checker!.getSymbolAtLocation(reference);
        if (!symbol || !symbol.declarations) {
            return;
        }
        for (const declaration of symbol.declarations) {
            switch (declaration.kind) {
                case SyntaxKind.FunctionDeclaration:
                case SyntaxKind.MethodDeclaration:
                case SyntaxKind.ClassDeclaration:
                    if (declarations.indexOf(declaration) === -1) {
                        declarations.push(declaration);
                    }
                    break;
                case SyntaxKind.ImportEqualsDeclaration:
                    getForwardDeclarations((declaration as ImportEqualsDeclaration).moduleReference, declarations, callerFileName);
                    break;
                case SyntaxKind.VariableDeclaration:
                case SyntaxKind.PropertyDeclaration:
                    const variable = declaration as VariableDeclaration;
                    const initializer = variable.initializer;
                    if (initializer) {
                        if (initializer.kind === SyntaxKind.Identifier || initializer.kind === SyntaxKind.PropertyAccessExpression) {
                            getForwardDeclarations(initializer, declarations, callerFileName);
                        }
                    }
                    break;
            }
        }
    }

    function checkClassInstantiation(node: ClassDeclaration): string[] {
        let methodNames: string[] = [];
        const superClass = getClassExtendsHeritageElement(node);
        if (superClass) {
            const type = checker!.getTypeAtLocation(superClass);
            if (type && type.symbol) {
                const declaration = getDeclarationOfKind(type.symbol, SyntaxKind.ClassDeclaration) as ClassDeclaration;
                if (declaration) {
                    methodNames = checkClassInstantiation(declaration);
                }
            }
        }

        const members = node.members;
        if (!members) {
            return [];
        }
        const index = calledMethods.length;
        for (const member of members) {
            if (hasStaticModifier(member)) {
                continue;
            }
            if (member.kind === SyntaxKind.MethodDeclaration) { // called by super class.
                const methodName = unescapeLeadingUnderscores(getTextOfPropertyName(member.name!));
                if (methodNames.indexOf(methodName) !== -1) {
                    visitBlock((member as MethodDeclaration).body);
                }
            }
            if (member.kind === SyntaxKind.PropertyDeclaration) {
                const property = member as PropertyDeclaration;
                visitExpression(property.initializer);
            }
            else if (member.kind === SyntaxKind.Constructor) {
                const constructor = member as ConstructorDeclaration;
                visitBlock(constructor.body);
            }
        }

        for (let i = index; i < calledMethods.length; i++) {
            const method = calledMethods[i];
            for (const memeber of members) {
                if (memeber === method) {
                    const methodName = unescapeLeadingUnderscores(getTextOfPropertyName(method.name));
                    methodNames.push(methodName);
                }
            }
        }
        if (index === 0) {
            calledMethods.length = 0;
        }
        return methodNames;
    }

    function visitBlock(block?: Block): void {
        if (!block || visitedBlocks.indexOf(block) !== -1) {
            return;
        }
        visitedBlocks.push(block);
        for (const statement of block.statements) {
            visitStatement(statement);
        }
        visitedBlocks.pop();
    }

    function visitVariableList(variables?: VariableDeclarationList) {
        if (!variables) {
            return;
        }
        variables.declarations.forEach(declaration => {
            visitExpression(declaration.initializer);
        });
    }

    function sortOnDependency(): SortingResult {
        const result: SortingResult = {} as any;
        result.sortedFileNames = [];
        result.circularReferences = [];
        pathWeightMap = {};
        const dtsFiles: SourceFile[] = [];
        const tsFiles: SourceFile[] = [];
        for (const sourceFile of sourceFiles) {
            const path = sourceFile.fileName;
            if (sourceFile.isDeclarationFile) {
                pathWeightMap[path] = 10000;
                dtsFiles.push(sourceFile);
                continue;
            }
            const references = updatePathWeight(path, 0, [path]);
            if (references.length > 0) {
                result.circularReferences = references;
                break;
            }
            tsFiles.push(sourceFile);
        }
        if (result.circularReferences.length === 0) {
            tsFiles.sort((a: SourceFile, b: SourceFile) => {
                return pathWeightMap[b.fileName] - pathWeightMap[a.fileName];
            });
            sourceFiles.length = 0;
            rootFileNames.length = 0;
            dtsFiles.concat(tsFiles).forEach(sourceFile => {
                sourceFiles.push(sourceFile);
                rootFileNames.push(sourceFile.fileName);
                result.sortedFileNames.push(sourceFile.fileName);
            });
        }
        pathWeightMap = {};
        return result;
    }

    function updatePathWeight(path: string, weight: number, references: string[]): string[] {
        if (pathWeightMap[path] === undefined) {
            pathWeightMap[path] = weight;
        }
        else {
            if (pathWeightMap[path] < weight) {
                pathWeightMap[path] = weight;
            }
            else {
                return [];
            }
        }
        const list = dependencyMap[path];
        if (!list) {
            return [];
        }
        for (const parentPath of list) {
            if (references.indexOf(parentPath) !== -1) {
                references.push(parentPath);
                return references;
            }
            const result = updatePathWeight(parentPath, weight + 1, references.concat(parentPath));
            if (result.length > 0) {
                return result;
            }
        }
        return [];
    }

    function getSourceFileOfNode(node: Node): SourceFile {
        while (node && node.kind !== SyntaxKind.SourceFile) {
            node = node.parent;
        }
        return node as SourceFile;
    }
}